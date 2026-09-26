(defrecord point [x y]) (defn move [p dx dy] (assoc p :x (+ (:x p) dx) :y (+ (:y p) dy)))
