;;; Copyright (C) 2011 Nils Bertschinger

;;; This file is part of Probabilistic-Clojure

;;; Probabilistic-Clojure is free software: you can redistribute it and/or modify
;;; it under the terms of the GNU Lesser General Public License as published by
;;; the Free Software Foundation, either version 3 of the License, or
;;; (at your option) any later version.

;;; Probabilistic-Clojure is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;; GNU Lesser General Public License for more details.

;;; You should have received a copy of the GNU Lesser General Public License
;;; along with Probabilistic-Clojure.  If not, see <http://www.gnu.org/licenses/>.

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

(defn indexed
  "Returns a new collection containing index-value pairs for each value
in the given collection."
  [coll]
  (map vector (iterate inc 0) coll)) 
