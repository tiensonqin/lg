# LG 类型推导现状评估报告

日期：2026-09-26，基于 lg @ a784f453。

## 结论先行

当前实现**不是** HM（Hindley–Milner）推导。它是一个以 `refine_type` 双向合并 +
顺序扫描为主的特判引擎，配合一个"显式替换表"式的 unify，再用至多 16 轮
全量"证据稳定化"补偿顺序依赖。后果正是用户感知到的三点：

1. **大量惯用写法需要 type hint**——25 条最普通的新手写片段里 4 条编译失败
   （16%），失败信息还会泄漏内部变量名（`param/g25`）。
2. **编译速度被结构性地拖慢**——每个类型都是不可变树、每次合一都全量套用
   substitution，外加多趟重编译兜底。
3. **生成代码写放大严重**——能力证据以 witness pair 进入参数 ABI（每个
   seqable 参数变 `(xs__seq, xs)` 两个值），每次关键字字段访问生成一个全新的
   名义 record 类型，默认 `--compile-files-from` 输出会整段重发 stdlib
   前缀（3 行源文件产出 11,244 行 / 580KB .ml）。

---

## 1. 现状架构

```
Ast.form
  → infer_params (src/type_inference.ml, ~9.3k 行；主函数单个 ~7k 行)
      对函数体做"逐形扫描 + 就地改写 (string * ty) 关联表"
  → refine_type (src/type_inference_core.ml, ~700 行特判合并)
      把"新旧两个候选类型"合并成一个——本质是半格 join，不是合一
  → Type_solver.unify (src/type_solver.ml)
      持久化 substitution map 版本合一；能力约束编码进类型内部
  → toolchain.stabilize_typecheck
      检测声明 ABI 变化则整批重编译，上限 16 趟
  → OCaml Parsetree → compiler-libs 终检
```

关键文件规模：

| 文件 | 行数 | 角色 |
|---|---:|---|
| `call_elaborator.ml` | 23,816 | 调用 elaboration + 适配 + witness 生成 |
| `type_inference.ml` | 9,318 | 形参/函数体推导（单函数 ~7k 行）|
| `types.ml` | 2,101 | 类型工具 + 约束编码/解码（字符串名约定）|
| `type_inference_core.ml` | 1,063 | `refine_type` 合并引擎 |
| `type_solver.ml` | 960 | substitution 合一器 |
| `special_form_elaborator.ml` | 5,573 | special form |

## 2. 核心问题

### 2.1 推导本体不是合一，而是顺序敏感的"合并"

`refine_type existing inferred` 是一条几百分支的特判链，语义是"把两个证据
捏成一个类型"。它：

- **顺序依赖**：`refine_type a b ≠ refine_type b a` 的分支大量存在
  （例如 `| existing, _ -> existing` 兜底）。同一函数把两个调用点调换顺序，
  推导结果可变。
- **静默吞掉冲突**：`refine_nonmatching_type` 末尾 `| existing, _ -> existing`
  直接把不兼容证据丢弃而不是报错，错误要么消失、要么推迟到 OCaml 终检，
  以 `LG4000`（指向生成代码而非源码）的形式爆出来。
- **无主类型保证**：HM 的本质是"每个 metavar 只有一个解"。这里形参类型是
  一张 assoc list 上被反复 replace 的槽位，后写覆盖先写，证据之间没有
  交/并的格结构保证。

### 2.2 约束被编码进类型语法内部

能力约束（seqable / contains / truthy / printable / hashable / comparable /
array_index / symbol_predicate / protocol / open_boundary）不是约束列表里的
一等数据，而是塞进 `ty` 里：`TConstraint (...)`，或以 `TOcaml_app` 的魔法
字符串名（`"__lg_next_seq"`、`"Lg_runtime.Runtime_transient.map"` 等）表示。

后果：

- 每个消费 `ty` 的模块都必须反向解析这些字符串；`types.ml` 里几十个
  `*_constraint_info` 解码器，`type_inference.ml`/`call_elaborator.ml`
  合计 ~760 处 constraint 字面量出现点。
- "类型"与"对类型的要求"混在同一棵树里，合一和展示都被污染——错误信息
  里直接泄漏 `param/g0`、`__lg_callable_expression_1` 这类内部名。

### 2.3 substitution-map 合一器：正确性 + 性能双输

`type_solver.ml` 用 `Persistent_hash_map` substitution 穿线：

- `apply` 每次合一调用都要对整棵类型树做一次"是否被 substitution 触及"
  的预扫描（另有 2048 节点预算 + 物理缓存两项补丁式优化，说明这里
  已经被性能追过一次）。OCaml 自身实现用 **就地绑定的 metavar + level**，
  `bind`/`apply` 是 O(1)。
- `TVar`（声明类型参数，语义上 rigid）与 `TMeta`（推导变量）走同一张
  substitution 表——`unify` 可以直接给 `Declared name` 绑定一个具体类型，
  rigid 性靠各调用点"记得丢弃"维持，而非由 solver 结构性保证。
- `TUnknown` 与任何东西合一都返回 `Ok`——"还没推出来"和"可以是任意类型"
  混为一谈，未知量变成静默通配。
- `generalize` 把类型里**所有**自由变量（含 Declared）量化成 `g0、g1…`
  名字。没有 level 概念，量化范围正确性靠上层约定。

### 2.4 16 趟证据稳定化是顺序依赖的显性症状

`stabilize_typecheck` 因为单趟推导无法得到稳定的声明 ABI（行类型、
overload 行、协议证据），被迫：跑一遍 → 比较每个声明的 ABI → 有变化就
以新环境重跑 → 至多 16 趟后报 `"type evidence did not stabilize"`。

这本质上是"推导结果依赖处理顺序"的补丁。HM 环境里同一个 letrec 组
约束一次求解、结果唯一，根本不需要这个外循环。它同时是编译耗时和
一类特有失败（不收敛）的来源。

### 2.5 能力证据的 witness-pair ABI = 运行时 + 代码双放大

`(map inc xs)` 里 `xs` 拿到 seqable 约束后，函数参数被改写成
`(xs__seq, xs)` 二元组——第一个分量是一个 `t -> t Seq.t` 适配闭包：

```ocaml
let clojure_zip_sum (xs__seq, xs) = ...
S.map clojure_zip_add_two (xs__seq xs)
```

每个调用点构造 `(S.of_vector, v)`；`str` 这类 printable 参数甚至带
两个 witness（`(name__print, name__pr), name`）。每个泛型参数一次调用
就多分配一到两个闭包。

### 2.6 匿名 nominal record = 结构性代码被名义化切碎

`(:name m)`、`(-> m :a :b :c)` 这类字段观察，每处生成一个新 nominal
record：

```ocaml
type nonrec 'a0 clojure_zip_getname_row0 = { name : 'a0 }
type nonrec 'g30 t1 = { a : 'g30 t2 }          (* (-> m :a :b :c) *)
type nonrec 'g30 t2 = { b : 'g30 }
```

12 行源文件产出 45 行 OCaml、3 个新类型。更糟的是这些是**名义类型**：
另一处同样观察 `:name` 的函数会得到不同的 `row1`，两者不能互换——
结构相同的代码被切碎成不兼容的类型身份，正是"写起来各种编译失败"
的直接来源之一。

### 2.7 未约束参数的暗坑：悄悄落进 Runtime_dynamic

```clojure
(defn nested [m] (get-in m [:a :b]))
```

生成：

```ocaml
let clojure_zip_nested m =
  Lg_runtime.Runtime_dynamic.get
    (Lg_runtime.Runtime_dynamic.get m (Runtime_dynamic.keyword ":a")) ...
```

`m` 没有任何约束 ⇒ 落成 `Runtime_dynamic.t` 动态 map 取值——这正是
design.md "禁止隐性 dynamic" 条款想禁止的行为，现状却能静默通过编译，
性能与静态保证一起流失。

## 3. 实测数据

环境：`opam switch 5.5.0`，lg @ a784f453。

| 指标 | 实测 |
|---|---|
| stdlib 全量编译（22 文件 / 14,115 行 → 11,237 行 .ml）| ~2.5 s（热，排除编译器自身构建）|
| 单个小文件编译（chunk-from stdlib state）| ~0.55 s 冷 / ~0.06–0.08 s 缓存命中 |
| `--compile-files-from` 3 行源 → 输出 .ml | 11,244 行 / 580 KB（整段重发前缀）|
| chunk 模式 12 行源 → 输出 .ml | 45 行（含 3 个匿名 record 类型 + witness pair）|
| 惯用片段无 hint 编译成功率（25 例）| 84%（失败例见下）|
| 证据稳定化趟数上限 | 16；超限报 `"type evidence did not stabilize"` |

无 hint 失败样例（最小复现）：

```clojure
(defn concat-p [xs ys] (concat xs ys))
;; concat expects collections, got param/g0        ← 内部变量名泄漏

(defn select-sub [m] (select-keys m [:a :b]))
;; select-keys expects a map                        ← 对未约束形参不会补 map 约束

(defn mapvals [m f] (into {} (map (fn [[k v]] [k (f v)]) m)))
;; heterogeneous vector has element types param/g13 | param/g2  ← vector/tuple 歧义

(defn kw-or-call [m k] ((or k :default) m))
;; __lg_callable_expression_1 is not callable       ← or 结果的可调用性不回传
```

这些都是 HM + 受限约束求解下应当成功的代码。

## 4. 对四个目标的根因映射

| 目标 | 现状根因 |
|---|---|
| 多数情况不用 hint | 无主类型 + 顺序合并：证据不足时不会"挂着待解约束继续"，而是当场失败或静默选择 |
| 正确性 | `refine_type` 吞冲突、`TUnknown` 万能合一、`Declared` rigid 变量可被绑值；冲突推迟到 OCaml 终检报错（LG4000，无源码定位） |
| 编译极快 | substitution-map 全量套用 + 类型树不可变反复复制 + 至多 16 趟整批重编译 |
| 写放大小 | witness-pair ABI、每处字段观察一个 nominal 匿名类型、输出整段重发前缀、stdlib state Marshal 2.6MB |

## 5. 建议的重写方向（详见后续 design doc）

把"推导"改成教科书式约束生成/求解两段式：

1. **类型数据结构不动**（`ty` 词汇保留），但 metavar 改为**可变的
   union-find + level**（OCaml `typ` 的 `Tvar {level}` 同款），合一不再
   复制类型树。
2. **约束作为一等数据**：`constraint list` 附着在 metavar 上，而不是编码进
   `ty`。能力约束（seqable/truthy/printable/...）保留语义，但作为延迟求解的
   待定约束；在 `defn` 边界一般化成 witness 参数（保留 ABI）或拒绝。
3. **let/loop/defn 边界做 level 化 generalization + value restriction**：
   得到主类型，`concat xs xs` 这类代码自动得到
   `seqable<'a> -> seqable<'a> -> seq<'a>`。
4. **删除 16 趟稳定化**：同层递归组一次约束求解。
5. **结构性 record 统一为 open row**（方向类似 OCaml object row / Elm
   record），不再每处生成名义类型；只有 `defrecord` 显式声明才是名义。
6. 未约束集合参数禁止落成 `Runtime_dynamic`——要么推迟为泛型约束，要么
   按 design.md 报错。

这个方向同时打击四个目标：主类型 → 少 hint；合一且顺序无关 → 正确 +
删趟数；O(1) 绑定 → 快；row 复用 + 无整段重发 → 写放大降。

## 6. 已知风险

- `call_elaborator.ml`（23.8k 行）把核心库 dispatch 与类型适配缠在一起，
  推导换心后这层仍然是最重的维护热点；第一阶段不动它，只让它消费新推导
  结果。
- witness ABI 是已发布的 .mli 契约面：换 ABI 要同时改 runtime 与所有
  下游 chunk 编译方式。第一步保留 `(seq_adapter, value)` 形状，只改变
  "何时生成"。
- 匿名 nominal record 在 .mli/缓存中被引用过，统一为 open row 需要注意
  向后兼容（旧 state 无法复用，直接作废）。

## 7. 后续步骤

1. `docs/` 下补一份新推导设计 + 验收标准（hint-free 成功率 / 编译耗时 /
   生成行数比 / 测试回归为 0）。
2. 先写 eval corpus（惯用片段集 + chat@f83c217 全量语料）跑基线。
3. 分阶段落地，每阶段过完整测试套件。
