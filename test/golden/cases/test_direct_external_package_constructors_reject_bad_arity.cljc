;; golden: bare

(require [ocaml.package/unix]
            [ocaml.Unix :as unix])
(def address (unix/ADDR_UNIX))
