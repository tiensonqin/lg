(defn loop-sum [xs] (loop [acc 0 rest-xs xs] (if (empty? rest-xs) acc (recur (+ acc (first rest-xs)) (rest rest-xs)))))
