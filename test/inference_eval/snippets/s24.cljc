(defn update-counter [m] (update m :count (fn [c] (+ (or c 0) 1))))
