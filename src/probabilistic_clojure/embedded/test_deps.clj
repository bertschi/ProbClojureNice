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
      :doc "Tests for probabilistic-clojure.embedded.
Checks dependency tracking between choice points"}
  probabilistic-clojure.embedded.test-deps
  (:use clojure.test)
  (:use probabilistic-clojure.embedded.api))

(in-ns 'probabilistic-clojure.embedded.test-deps)

;;; TODO: use testing framework and write real unit tests!!!

(defn deps-fixture [dep-test-func]
  (with-fresh-store {}
    (dep-test-func)))

(use-fixtures :each deps-fixture)

(defn check-store
  "Pass sets of cp-names for the corresponding entries in the global-store.
Those are then tested against the current store, i.e. (is (= <store value> <passed value>))."
  [{:keys [recomputed newly-created possibly-removed]}]
  (are [store-key val] (= (fetch-store store-key) val)
       :recomputed       recomputed
       :newly-created    newly-created
       :possibly-removed possibly-removed))

(defn check-cps [tag & cp-data]
  (doseq [[cp-name v dependents depends-on] cp-data]
    (let [cp (fetch-store :choice-points (get cp-name))
	  msg (str tag ": checking choice point " cp-name)]
      (is (= (:recomputed cp) v) msg)
      (is (= (:dependents cp) dependents) msg)
      (is (= (:depends-on cp) depends-on) msg))))
    
(defn set-value! [cp val]
  (assoc-in-store! [:choice-points (:name cp) :recomputed] val))

(defn refresh []
  (reset! *global-store*
	  (fresh-state (fetch-store :choice-points))))

(deftest dynamic-dependencies
  (let [a (det-cp :a true)
	b (det-cp :b (list :hello (gv a)))
	c (det-cp :c (if (gv a)
		       (list (gv b) :c)
		       :nope))

	[na nb nc] (map :name [a b c])]
    ;; check initial values
    (check-cps :initial
     [na true                         #{nb nc} #{}]
     [nb (list :hello true)           #{nc}    #{na}]
     [nc (list (list :hello true) :c) #{}      #{na nb}])
    (check-store {:recomputed    #{na nb nc}
		  :newly-created #{na nb nc}
		  :possibly-removed #{}})
    ;; now update b and recompute
    (refresh)    
    (set-value! b :huhu)
    (recompute-value c)
    (check-cps :huhu
     [na true            #{nb nc} #{}]
     [nb :huhu           #{nc}    #{na}]
     [nc (list :huhu :c) #{}      #{na nb}])
    (check-store {:recomputed    #{nc}
    		  :newly-created #{}
    		  :possibly-removed #{}})
    ;; setting a to false changes dependencies
    (refresh)
    (set-value! a false)
    (recompute-value c)
    (check-cps :a-false
     [na false #{nb nc} #{}]
     [nb :huhu #{}      #{na}]
     [nc :nope #{}      #{na}])
    (check-store {:recomputed    #{nc}
    		  :newly-created #{}
    		  :possibly-removed #{nb}})
    ;; now changing b has not much effect
    (refresh)    
    (set-value! b :nowhere)
    (recompute-value c)
    (check-cps :nowhere
     [na false    #{nb nc} #{}]
     [nb :nowhere #{}      #{na}]
     [nc :nope    #{}      #{na}])
    (check-store {:recomputed    #{nc}
    		  :newly-created #{}
    		  :possibly-removed #{}})
    ;; now remove b from the store and set a back to true
    ;; dependencies change again and b is re-created
    (refresh)
    (update-in-store! [:choice-points] dissoc nb)
    (set-value! a true)
    (recompute-value c)
    (check-cps :init-again
     [na true                         #{nb nc} #{}]
     [nb (list :hello true)           #{nc}    #{na}]
     [nc (list (list :hello true) :c) #{}      #{na nb}])
    (check-store {:recomputed    #{nb nc}
    		  :newly-created #{nb}
    		  :possibly-removed #{}})))

(deftest propagation-consistency-1
  (let [a (det-cp :a :a)
	b (det-cp :b (list :b (gv a)))
	c (det-cp :c (list :c (gv b) (gv a)))
	p (flip-cp :p (if (gv a) 0.0 1.0))
	d (det-cp :d (list :d (gv p) (gv c)))
	e (det-cp :e (list :e (gv p)))

	[na nb nc np nd ne] (map :name [a b c p d e])]
    (check-cps :initial
     [na :a #{nb nc np} #{}]
     [nb '(:b :a) #{nc} #{na}]
     [nc '(:c (:b :a) :a) #{nd} #{na nb}]
     [np '(0.0) #{nd ne} #{na}]
     [nd '(:d false (:c (:b :a) :a)) #{} #{nc np}]
     [ne '(:e false) #{} #{np}])
    (set-value! a nil)
    (propagate-change-to
     (fetch-store :choice-points (get na) :dependents))
    (check-cps :initial
     [na nil #{nb nc np} #{}]
     [nb '(:b nil) #{nc} #{na}]
     [nc '(:c (:b nil) nil) #{nd} #{na nb}]
     [np '(1.0) #{nd ne} #{na}] ;; the value false is not changed, even though it has prob. zero now!
     [nd '(:d false (:c (:b nil) nil)) #{} #{nc np}]
     [ne '(:e false) #{} #{np}])))

(deftest propagation-consistency-2
  (let [c (atom 0)
	a (det-cp :a true)
	b (det-cp :b (if (gv a)
		       :b-true
		       (list :a-false (gv @c))))]
    (reset! c (det-cp :c (if (gv a)
			   (list :a-true (gv b))
			   :c-false)))
    (let [[na nb nc] (map :name [a b @c])]
      (check-cps :initial
       [na true #{nb nc} #{}]
       [nb :b-true #{nc} #{na}]
       [nc '(:a-true :b-true) #{} #{na nb}])
      (refresh)
      (set-value! a false)
      (propagate-change-to
       (fetch-store :choice-points (get na) :dependents))
      (check-cps :flip
       [na false #{nb nc} #{}]
       [nb '(:a-false :c-false) #{} #{na nc}]
       [nc :c-false #{nb} #{na}])
      (refresh)
      (set-value! a true)
      (propagate-change-to
       (fetch-store :choice-points (get na) :dependents))
      (check-cps :flip-flip
       [na true #{nb nc} #{}]
       [nb :b-true #{nc} #{na}]
       [nc '(:a-true :b-true) #{} #{na nb}]))))