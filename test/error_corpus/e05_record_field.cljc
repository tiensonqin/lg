(defrecord User [name age])
(defn greet [^:User u] (str "hi " (:name u)))
(def bad (greet {:name "a"}))
