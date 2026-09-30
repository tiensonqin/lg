(def x (let [{:keys [age] :or [age 0]} {:name "Ada"}] age))
