;; golden: bare

(defprotocol LookupProtocol
  (lookup-value [receiver key] [receiver other]))
