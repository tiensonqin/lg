;; golden: bare

(ns app.search
  (:refer-clojure :exclude [find]))
(def result (find (fn [value] true) [1]))
