#!/bin/bash
mk() { cat > "$1.cljc"; }
mk s01 <<'E'
(defn add [a b] (+ a b))
E
mk s02 <<'E'
(defn apply-inc [xs] (map inc xs))
E
mk s03 <<'E'
(defn sum-by [f xs] (reduce (fn [a x] (+ a (f x))) 0 xs))
E
mk s04 <<'E'
(defn concat-p [xs ys] (concat xs ys))
E
mk s05 <<'E'
(defn both [xs] [(first xs) (last xs)])
E
mk s06 <<'E'
(defn keys-of [m] (keys m))
E
mk s07 <<'E'
(defn assoc-x [m] (assoc m :x 1))
E
mk s08 <<'E'
(defn swap-in [a] (swap! a inc))
E
mk s09 <<'E'
(defn push-vec [v x] (conj v x))
E
mk s10 <<'E'
(defn str-join [xs] (clojure.string/join "," xs))
E
mk s11 <<'E'
(defn count-twice [xs] (+ (count xs) (count xs)))
E
mk s12 <<'E'
(defn print-ret [x] (println x) x)
E
mk s13 <<'E'
(defn when-nil [x] (when (nil? x) 0))
E
mk s14 <<'E'
(defn if-some-v [o] (if-some [v o] v 0))
E
mk s15 <<'E'
(defn sort-uniq [xs] (sort (distinct xs)))
E
mk s16 <<'E'
(defn take-2 [xs] (take 2 xs))
E
mk s17 <<'E'
(defn mapvals [m f] (into {} (map (fn [[k v]] [k (f v)]) m)))
E
mk s18 <<'E'
(defn filter-odd [xs] (filter odd? xs))
E
mk s19 <<'E'
(defn repeat-call [f n] (repeatedly n f))
E
mk s20 <<'E'
(defn deref-add [r s] (+ @r @s))
E
mk s21 <<'E'
(defn interpose-x [xs] (interpose :sep xs))
E
mk s22 <<'E'
(defn zipmap-k [ks vs] (zipmap ks vs))
E
mk s23 <<'E'
(defn select-sub [m] (select-keys m [:a :b]))
E
mk s24 <<'E'
(defn update-counter [m] (update m :count (fn [c] (+ (or c 0) 1))))
E
mk s25 <<'E'
(defn kw-or-call [m k] ((or k :default) m))
E
mk s26 <<'E'
(defn update-nested [m] (update-in m [:a :b] inc))
E
mk s27 <<'E'
(defn merge-maps [a b] (merge a b))
E
mk s28 <<'E'
(defn dissoc-k [m] (dissoc m :x))
E
mk s29 <<'E'
(defn some-pred [xs] (some even? xs))
E
mk s30 <<'E'
(defn every-pred [xs] (every? pos? xs))
E
mk s31 <<'E'
(defn apply-sum [f args] (apply f args))
E
mk s32 <<'E'
(defn partial-add [x] (partial + x))
E
mk s33 <<'E'
(defn comp-fns [f g x] ((comp f g) x))
E
mk s34 <<'E'
(def delay-v (delay (+ 1 2)))
E
mk s35 <<'E'
(defn letfn-mutual [n] (letfn [(even-f [x] (if (zero? x) true (odd-f (dec x)))) (odd-f [x] (if (zero? x) false (even-f (dec x))))] (even-f n)))
E
mk s36 <<'E'
(defn loop-sum [xs] (loop [acc 0 rest-xs xs] (if (empty? rest-xs) acc (recur (+ acc (first rest-xs)) (rest rest-xs)))))
E
mk s37 <<'E'
(defn cond-chain [x] (cond (< x 0) :neg (> x 0) :pos :else :zero))
E
mk s38 <<'E'
(defn case-x [x] (case x :a 1 :b 2 0))
E
mk s39 <<'E'
(defn try-parse [s] (try (int s) (catch :default _e 0)))
E
mk s40 <<'E'
(defn doseq-sum [xs] (let [acc (atom 0)] (doseq [x xs] (swap! acc + x)) @acc))
E
mk s41 <<'E'
(defn for-list [xs] (for [x xs] (* x x)))
E
mk s42 <<'E'
(defn destruct-map [m] (let [{:keys [a b]} m] (+ a b)))
E
mk s43 <<'E'
(defn arg-count [& xs] (count xs))
E
mk s44 <<'E'
(defn vec-of-vec [xs] (mapv (fn [x] [x]) xs))
E
mk s45 <<'E'
(defn juxt-min-max [xs] ((juxt min max) xs))
E
mk s46 <<'E'
(defrecord point [x y]) (defn move [p dx dy] (assoc p :x (+ (:x p) dx) :y (+ (:y p) dy)))
E
mk s47 <<'E'
(defn re-req [s] (re-find #"\\d+" s))
E
mk s48 <<'E'
(defn name-of [x] (name x))
E
mk s49 <<'E'
(defn kw-hof [f m] (f (:key m)))
E
mk s50 <<'E'
(defn transducer-take [xs] (into [] (comp (map inc) (filter even?)) xs))
E
