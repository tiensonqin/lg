(defn apply-sum [f args] (apply f args))
(def s (apply-sum + [1 2]))
