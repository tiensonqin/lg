(defn letfn-mutual [n] (letfn [(even-f [x] (if (zero? x) true (odd-f (dec x)))) (odd-f [x] (if (zero? x) false (even-f (dec x))))] (even-f n)))
