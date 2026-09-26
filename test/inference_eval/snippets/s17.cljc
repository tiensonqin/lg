(defn mapvals [m f] (into {} (map (fn [[k v]] [k (f v)]) m)))
