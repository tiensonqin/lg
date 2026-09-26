(defn doseq-sum [xs] (let [acc (atom 0)] (doseq [x xs] (swap! acc + x)) @acc))
