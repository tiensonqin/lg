(defrecord User [name])
(defn names [users] (map :name users))
(def bad (names [1 2 3]))
