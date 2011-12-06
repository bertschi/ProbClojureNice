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
      :doc "Tests for probabilistic-clojure.embedded"}
  probabilistic-clojure.embedded.tests
  (:use probabilistic-clojure.embedded.api
	probabilistic-clojure.utils.sampling
	probabilistic-clojure.embedded.demos))

;;; TODO: use testing framework and write real unit tests!!!

(defn test-dynamic-dependencies []
  (reset-store)
  (let [a (det-cp :a true)
	b (det-cp :b (list :hello (gv a)))
	c (det-cp :c
	   (do (println "Here")
	       (if (gv a) (list (gv b) :c) :nope)))
	show-cps (fn []
		   (println "Recomputed: " (:recomputed @*global-store*))
		   (println "Newly created: " (:newly-created @*global-store*))
		   (println "Possibly removed: " (:possibly-removed @*global-store*))
		   (doseq [[name cp] (:choice-points @*global-store*)]
		     (println name ": " (:recomputed cp)
			      " dependents " (:dependents cp)
			      " depends on " (:depends-on cp))))
	set-value! (fn [cp val]
		     (swap! *global-store*
			    assoc-in [:choice-points (:name cp) :recomputed] val))
	refresh (fn [] (swap! *global-store* (constantly
					      (fresh-state (:choice-points @*global-store*)))))]
		     
    (show-cps)
    (refresh)    
    (set-value! b :huhu)
    (recompute-value c)
    (show-cps)
    (refresh)
    (set-value! a false)
    (recompute-value c)
    (show-cps)
    (refresh)    
    (set-value! b :nowhere)
    (recompute-value c)
    (show-cps)
    (refresh)
    (swap! *global-store* update-in [:choice-points] dissoc (:name b))
    (set-value! a true)
    (recompute-value c)
    (show-cps)))

(defn test-bayes-net [bayes-net]
  (density (monte-carlo-sampling 25000 bayes-net)))