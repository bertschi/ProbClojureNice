(ns
    ^{:author "Nils Bertschinger"
      :doc "Small collections of little helpers"}
  probabilistic-clojure.utils.stuff)

(defn ensure-list [x]
  (if (seq? x) x (list x)))

(defn error [& args]
  (throw (Error. (apply str args))))

(defn transpose
  "Transpose a list of lists, i.e. (transpose [[1 2] [3 4] [5 6]]) = [[1 3 5] [2 4 6]]"
  [lls]
  (apply map list lls))
