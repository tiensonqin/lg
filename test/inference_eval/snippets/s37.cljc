(defn cond-chain [x] (cond (< x 0) :neg (> x 0) :pos :else :zero))
