;; .cljc reader conditionals — native is the default target
(let [v #?(:native 10 :js 20)]
  (println (str "v: " v)))
(println #?(:native "ran on ocaml" :js "ran on js"))
(println (str #?@(:native ["sp" "liced"] :js ["x"])))
;; unmatched branch with no default vanishes
(let [w (list #?(:js 99) 2 3)]
  (println (str "w: " w)))
