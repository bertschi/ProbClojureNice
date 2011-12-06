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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Probabilistic programming using constraint propagation
;;;; to efficiently track dependencies between choice points
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ns
    ^{:author "Nils Bertschinger"
      :doc "Part of probabilistic-clojure.embedded. Collection of demo programs."}
  probabilistic-clojure.embedded.demos
  (:use [probabilistic-clojure.embedded.api :only (det-cp gv trace-failure)]
	[probabilistic-clojure.embedded.choice-points :only (flip-cp)]))

(in-ns 'probabilistic-clojure.embedded.demos)

;;; Simple Bayes net as a first example

(defn noisy-or [x y]
  (det-cp :noisy-or
   (or (and (gv x) (gv (flip-cp :flip9 0.9)))
       (and (gv y) (gv (flip-cp :flip8 0.8)))
       (gv (flip-cp :flip1 0.1)))))

(defn grass-bayes-net []
  (det-cp :grass-bayes-net
   (let [rain (flip-cp :rain 0.3)
	 sprinkler (flip-cp :sprinkler 0.5)
	 grass-is-wet (gv (noisy-or rain sprinkler))]
     (when-not grass-is-wet
       (trace-failure))
     (gv rain))))

(defn grass-bayes-net-fixed []
  (det-cp :grass-bayes-net-fixed
   (let [rain      (gv (flip-cp :rain      0.3))
	 sprinkler (gv (flip-cp :sprinkler 0.5))
	 noise-x   (gv (flip-cp :noise-x   0.9))
	 noise-y   (gv (flip-cp :noise-y   0.8))
	 noise-z   (gv (flip-cp :noise-z   0.1))]
     (if (or (and rain      noise-x)
	     (and sprinkler noise-y)
	     noise-z)
       rain
       (trace-failure)))))

