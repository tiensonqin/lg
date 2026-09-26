(defn sum-by [f xs] (reduce (fn [a x] (+ a (f x))) 0 xs))
