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
      :doc "This library implements Metropolis-Hastings sampling for
the probability monad. The system allows to condition and memoize
choice points and can be extended by user defined probabilistic choices."}
  probabilistic.metropolis-hastings
  (:use [clojure.contrib.monads :only (defmonad)])
  (:use [incanter.core :only (gamma)]
	[incanter.stats :only (sample-normal pdf-normal sample-dirichlet sample-beta pdf-beta)]))

(in-ns 'probabilistic.metropolis-hastings)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Basic data structures and utilities
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord ChoicePoint
  [sampler get-log-prob proposer get-log-proposal-prob])

(defrecord DBentry
  [value log-lik status type params choice-point])

(defn- activate [database addr]
  (assoc-in database [addr :status] :active))

(defn- inactivate-all [database]
  (into {} (for [[addr entry] database]
	     [addr (assoc entry :status :inactive)])))

(defn- clean-db-back [database]
  (reduce (fn [[db log-bwd-prob] [addr entry]]
	    (if (= (:status entry) :active)
	      [(assoc db addr entry) log-bwd-prob]
	      [db (+ log-bwd-prob (apply (:get-log-prob (:choice-point entry))
					 (:value entry) (:params entry)))]))
	  [{} 0] (seq database)))

(defn- ensure-list [x]
  (if (seq? x) x (list x)))

(defn sample-from
  "Sample from a discrete distribution implemented as a hash-map from
values to probabilities."
  [dist]
  (when (seq dist)
    (let [total (reduce + (vals dist))
	  threshold (rand)]
      (loop [cum-p 0
	     [[v p] & more] (seq dist)]
	(if (< threshold (+ cum-p p))
	  v
	  (recur (+ cum-p p) more))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The monadic interface
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def log-prob-zero (Math/log 0))

(defn- m-result-MH [v]
  (fn [addr database log-fwd-prob log-lik mems]
    ;; there is no choice here, so just return everything directly
    [v log-lik database log-fwd-prob mems]))

(def m-zero-MH
  (fn [addr database log-fwd-prob log-lik mems]
    ;; invalidate this trace
    [:invalid log-prob-zero database log-fwd-prob mems]))

(defn- m-bind-MH [m f]
  (fn [addr database log-fwd-prob log-lik mems]
    ;; here we first run the monad m and then
    ;; plug the values into the continuation f
    (let [[v log-lik database log-fwd-prob mems]
	  (m (cons "BIND-M" addr) database log-fwd-prob log-lik mems)]
      (if (= v :invalid)
	(m-zero-MH (cons "BIND-F" addr) database log-fwd-prob log-lik mems)
	((f v) (cons "BIND-F" addr) database log-fwd-prob log-lik mems)))))

;; Definition of our monad (note that no implementation of m-plus is provided!)
(defmonad probabilistic-sampling-m
  [m-result m-result-MH
   m-bind   m-bind-MH
   m-zero   m-zero-MH])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; User functions for defining choice points and running probabilistic programs
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-choice-point
  "Allows to define a new probabilistic choice point by providing a function
for sampling and calculating the log-likelihood.
See the source code of flip for an example."
  ([name params sampler get-log-prob]
     (make-choice-point name params
			sampler get-log-prob
			(fn [val & args] (apply sampler args))
			(fn [new-val old-val & args] (apply get-log-prob new-val args))))
  ([name params sampler get-log-prob proposer get-log-proposal-prob]
     (fn [addr database log-fwd-prob log-lik mems]
       ;; this function runs the choice-point with entries from the database and updates the trace
       (let [addr (cons name addr)
	     create-new-randomness
	     (fn []
	       (let [val (apply sampler params)
		     ll  (apply get-log-prob val params)]
		 [val
		  (+ log-lik ll)
		  (assoc database addr
			 (DBentry. val ll :active name params
				   (ChoicePoint. sampler get-log-prob proposer get-log-proposal-prob)))
		  (+ log-fwd-prob ll) mems]))]				  
	 (if (contains? database addr)
	   (let [entry (database addr)]
	     (if (= (:params entry) params)
	       ;; we found an exact match, so just lookup the value
	       (let [val (:value entry)
		     ll  (apply (:get-log-prob (:choice-point entry)) val params)]
		 [val (+ log-lik ll) (activate database addr) log-fwd-prob mems])
	       ;; no exact match, we have to reweight the trace
	       (let [val (:value entry)
		     ll  (apply (:get-log-prob (:choice-point entry)) val params)]
		 (if (= ll log-prob-zero)
		   (create-new-randomness)
		   [val (+ log-lik ll)
		    (-> database
			(activate addr)
			(assoc-in [addr :log-lik] ll)
			(assoc-in [addr :params]  params))
		    log-fwd-prob mems]))))
	   ;; not in database, create new randomness
	   (create-new-randomness))))))

(defn- get-trace [m-MH database]
  (m-MH (list "TOP") database 0 0 {}))

(defn cond-data
  "Condition on a specific value of data.
This function must be applied to an elementary random choice point, e.g. (flip 0.6).
A trace running through this value is then weighted according to the likelihood of the data value."
  [choice val]
  (fn [addr database log-fwd-prob log-lik mems]
    (let [[[_ choice-entry] & more] (seq (get (get-trace choice {}) 2))
	  choice-point (:choice-point choice-entry)
	  ll (apply (:get-log-prob choice-point) val (:params choice-entry))]
      (assert (nil? more)) ; ensure that its was called on an elementary choice point
      [val (+ log-lik ll) database log-fwd-prob mems])))

(defmacro mem
  "Memoize a MH monadic value on some given arguments, i.e. if the same arguments
are encountered again it refers back to the original choice
point which was established for these arguments in the trace."
  [m-MH-form & add-args]
  `(fn [addr# database# log-fwd-prob# log-lik# mems#]
     (let [mem-addr# (list "MEMO" (str '~(first (ensure-list m-MH-form))) ~@(rest (ensure-list m-MH-form)) ~@add-args)
	   ;; now just redirect the choice point to the new address
	   ;; which identifies it according to its arguments
	   [val# ll# db# lfp# ms#] (~m-MH-form mem-addr# database# log-fwd-prob# log-lik# mems#)]
       (if (contains? mems# mem-addr#)
	 (do ;; (assert (= database# db#))
	   [val# log-lik# database# log-fwd-prob# (update-in ms# [mem-addr#] inc)])
	 [val# ll# db# lfp# (assoc ms# mem-addr# 1)]))))

(defn sample-traces
  ([m-MH]
     (println "Trying to find valid trace ...")
     (loop [[val log-lik database mems] (get-trace m-MH {})]
       (if (or (= val :invalid) (= log-lik log-prob-zero))
	 (recur (get-trace m-MH {}))
	 (do (println "Starting MH-sampling.")
	     (sample-traces m-MH database mems log-lik val 1 1)))))
  ([m-MH database mems log-lik val idx num-acc]
     (when (= (mod idx 500) 0)
       (println (str idx ": value " val " with log. likelihood " log-lik))
       (println (str "Accepted " num-acc " out of last 500 proposals")))
     (let [num-acc (if (= (mod idx 500) 0) 0 num-acc)
	   [addr entry] (rand-nth (for [[addr entry] database,
					en (repeat (if (contains? mems (rest addr))
						     (mems (rest addr))
						     1)
						   entry)]
				    [addr en]))
	   prop-val    (apply (:proposer (:choice-point entry)) (:value entry) (:params entry))
	   ll-prop-val (apply (:get-log-proposal-prob (:choice-point entry))
			      prop-val (:value entry) (:params entry))
	   ll-val      (apply (:get-log-proposal-prob (:choice-point entry))
			      (:value entry) prop-val (:params entry))
	   [next-val next-log-lik next-database log-fwd-prob next-mems]
	   (get-trace m-MH
		      (-> (inactivate-all database)
			  (assoc-in [addr :value] prop-val)
			  (assoc-in [addr :log-lik]
				    (apply (:get-log-prob (:choice-point entry)) prop-val (:params entry)))))]
       (if (= next-val :invalid) ; trace was rejected => retry
	 (lazy-seq (cons val (sample-traces m-MH database mems log-lik val (inc idx) num-acc)))
	 ; (recur m-MH database log-lik val)
	 (let [[next-database log-bwd-prob] (clean-db-back next-database)]
	   (if (< (Math/log (rand))
	   	  (+ (- next-log-lik log-lik)
	   	     (Math/log (/ (count database) (count next-database)))
	   	     (- ll-val ll-prop-val)
	   	     (- log-bwd-prob log-fwd-prob)))
	     (lazy-seq (cons next-val (sample-traces m-MH next-database next-mems
						     next-log-lik next-val
						     (inc idx) (inc num-acc))))
	     (lazy-seq (cons val (sample-traces m-MH database mems log-lik val (inc idx) num-acc)))))))))

(defn monte-carlo-sample [m-MH]
  (first (get-trace m-MH {})))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Definitions of useful basic choice points
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn flip [p]
  (make-choice-point "FLIP" [p]
		     (fn [p] (< (rand) p))
		     (fn [b p] (Math/log (if b p (- 1 p))))
		     (fn [b p] (not b))
		     (fn [new-b old-b p] (Math/log 1))))

(defn discrete [dist]
  (make-choice-point "DISCRETE" [dist]
		     (fn [dist] (sample-from dist))
		     (fn [x dist]
		       (if (contains? dist x)
			 (Math/log (dist x))
			 log-prob-zero))))

(defn gaussian [mu sdev]
  (let [proposal-sd 0.7]
    (make-choice-point "GAUSSIAN" [mu sdev]
		       (fn [mu sdev] (sample-normal 1 :mean mu :sd sdev))
		       (fn [x mu sdev] (Math/log (pdf-normal x :mean mu :sd sdev)))
		       (fn [x mu sdev] (sample-normal 1 :mean x :sd proposal-sd))
		       (fn [new-x old-x mu sdev]
			 (Math/log (pdf-normal new-x :mean old-x :sd proposal-sd 0.7))))))

(defn pdf-dirichlet [ps alphas]
  (let [norm (/ (reduce * (map gamma alphas))
		(gamma (reduce + alphas)))]
    (/ (reduce * (map (fn [p a] (Math/pow p (- a 1))) ps alphas))
       norm)))

(defn dirichlet [alphas]
  (let [proposal-alphas (fn [alphas]
			  (for [a alphas] (* 18 a)))]
    (make-choice-point "DIRICHLET" [alphas]
		       (fn [alphas] (first (sample-dirichlet 2 alphas)))
		       (fn [ps alphas] (pdf-dirichlet ps alphas))
		       (fn [ps alphas] (first (sample-dirichlet 2 (proposal-alphas ps))))
		       (fn [new-ps old-ps alphas]
			 (Math/log (pdf-dirichlet new-ps (proposal-alphas old-ps)))))))
