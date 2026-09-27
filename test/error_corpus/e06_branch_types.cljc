(defrecord User [name age])
(defn choose [^:bool flag] (if flag 1 "no"))
(def bad (choose 1))
