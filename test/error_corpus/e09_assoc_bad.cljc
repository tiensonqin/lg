(defrecord User [^:string name ^:int age])
(defn update-age [^:User u] (assoc u :age "old"))
