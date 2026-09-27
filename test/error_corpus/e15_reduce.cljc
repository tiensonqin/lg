(defn total [^:vector<int> xs] (reduce + 0 xs))
(def bad (total ["a" "b"]))
