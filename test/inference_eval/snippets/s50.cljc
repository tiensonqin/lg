(defn transducer-take [xs] (into [] (comp (map inc) (filter even?)) xs))
