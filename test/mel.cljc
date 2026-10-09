;; melange backend: :js ffi + reader conditionals, exercised via node
(ffi flr [:float] :float #?(:native {:native "floor"} :js {:js "floor" :scope ["Math"]}))
(ffi basename [:string] :string {:js "basename" :module "node:path"})
(extern-type jmap)
(ffi make-map [] :jmap {:js "Map" :kind :new})
(ffi size [:jmap] :int {:js "size" :kind :get})
(let [m (make-map)]
  (println (str "floor: " (flr 3.7) ", base: " (basename "/a/b.txt") ", size: " (size m))))
(println (str "v: " #?(:native 10 :js 20)))
(println #?(:native "native" :js "js"))
