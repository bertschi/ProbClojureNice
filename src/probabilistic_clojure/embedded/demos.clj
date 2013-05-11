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
  (:use [probabilistic-clojure.embedded.api :only (det-cp gv trace-failure cond-data memo metropolis-hastings-sampling def-prob-cp)]
	[probabilistic-clojure.utils.stuff :only (indexed)]
	[probabilistic-clojure.utils.sampling :only (sample-from density)]
	[probabilistic-clojure.embedded.choice-points
	 :only (flip-cp gaussian-cp dirichlet-cp discrete-cp dirichlet-process)]

	[incanter.core   :only (view)]
	[incanter.charts :only (histogram add-lines xy-plot)]
	[incanter.stats  :only (mean sample-normal pdf-normal)]))

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

(defn run-bayes-net [model]
  (density
   (take 7500 (drop 500 (metropolis-hastings-sampling model)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Gaussian mixture models
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn generate-data []
  (let [mu (fn [] (sample-from {-5 0.2, 0 0.7, 8 0.1}))]
    (lazy-seq (cons (sample-normal 1 :mean (mu))
		    (generate-data)))))

(def data (take 42 (generate-data)))

(defn mixture [comp-labels data]
  (let [comp-weights (dirichlet-cp :weights (for [_ comp-labels] 10.0))
	comp-mus (zipmap comp-labels
			 (for [label comp-labels] (gaussian-cp [:mu label] 0.0 10.0)))]
    (doseq [[idx point] (indexed data)]
      (let [comp (discrete-cp [:comp idx] (zipmap comp-labels (gv comp-weights)))]
	;;     mu-comp (det-cp [:mu-comp idx] (gv (get comp-mus (gv comp))))]
	;; (cond-data (gaussian-cp [:obs idx] (gv mu-comp) 1.0) point)
	(cond-data (gaussian-cp [:obs idx] (gv (get comp-mus (gv comp))) 1.0) point)))
    (det-cp :mixture
      [(into {} (for [[comp mu] comp-mus] [comp (gv mu)]))
       (gv comp-weights)])))

(defn mixture-memo [comp-labels data]
  (let [comp-weights (dirichlet-cp :weights (for [_ comp-labels] 10.0))]
    (doseq [[idx point] (indexed data)]
      (let [comp (discrete-cp [:comp idx] (zipmap comp-labels (gv comp-weights)))
	    comp-mu (memo [:mu idx] (gaussian-cp :mu 0.0 10.0) (gv comp))]
	(cond-data (gaussian-cp [:obs idx] (gv comp-mu) 1.0) point)))
    (det-cp :mixture
      [(into {} (for [comp comp-labels]
		  [comp (gv (memo [:mu comp] (gaussian-cp :mu 0.0 10.0) comp))]))
       (gv comp-weights)])))
       
(defn test-mixture [comp-labels model]
  (let [data-plot (histogram data :title "Dataset" :nbins 50 :density true)
	num-comp (count comp-labels)
	[comp-mus weights]  (last (take 7500 (metropolis-hastings-sampling (fn [] (model comp-labels data)))))
	mus (for [label comp-labels] (get comp-mus label))
	
	xs (range -10 10 0.01)

	comp-pdf (fn [i x]
		   (* (nth weights i) (pdf-normal x :mean (nth mus i) :sd 1)))
	mix-pdf  (fn [x] (reduce + (for [i (range num-comp)] (comp-pdf i x))))]
    ;; add the pdf of the fitted mixture
    (add-lines data-plot xs (map mix-pdf xs))
    ;; and all individual components to the plot
    (doseq [i (range num-comp)]
      (add-lines data-plot xs (map (partial comp-pdf i) xs)))
    (view data-plot)
    [weights mus]))

;;; now we collapse out the component assignments

(def-prob-cp collapsed-mixture-cp [comp-probs comp-models]
  :sampler [] [] ; just a dummy initialization ... no data drawn from model
  :calc-log-lik [xs]
  (let [sum (partial reduce +)]
    (sum (for [x xs]
	   (Math/log ; switch to log-probabilities
	    (sum (for [[p cm] (zipmap comp-probs comp-models)]
		   ;; component model is a function that calculates the
		   ;; probability for a given datapoint
		   (* p (cm x))))))))
  :proposer [_] (probabilistic-clojure.utils.stuff/error
		 "collapsed-mixture-cp does not implement a proposer!"))

(defn gaussian-comp-model [mu sdev]
  (fn [x] (pdf-normal x :mean mu :sd sdev)))

(defn mixture-collapsed [comp-labels data]
  (let [comp-weights (dirichlet-cp :weights (repeat (count comp-labels) 10.0))
	comp-mus     (for [label comp-labels]
		       (gaussian-cp [:mu label] 0.0 10.0))
	comp-models (det-cp :models
			    (doall (for [mu-cp comp-mus]
				     (gaussian-comp-model (gv mu-cp) 1.0))))]
    (cond-data (collapsed-mixture-cp :data (gv comp-weights) (gv comp-models))
	       data)
    (det-cp :mixture
      [(zipmap comp-labels (map gv comp-mus))
       (gv comp-weights)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Dirichlet process mixture model
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn mixture-DP [alpha data]
  (loop [points data
	 idx 0
	 comps (det-cp [:res 0] [0 {}])]
    (if (seq points)
      (let [mu-comp (dirichlet-process [::DP idx] alpha (gaussian-cp ::DP 0 15))]
	(cond-data (gaussian-cp [:mu idx] (gv mu-comp) 1.0) (first points))
	(recur (rest points) (inc idx)
	       (det-cp [:res (inc idx)]
		 (let [[num-comp comp-mus] (gv comps)
		       mu (gv mu-comp)
		       mu-count (get comp-mus mu 0)
		       comp-mus (assoc comp-mus mu (inc mu-count))]
		   [(count comp-mus) comp-mus]))))
      comps)))

(defn test-DP [alpha n]
  (let [res (metropolis-hastings-sampling (fn [] (mixture-DP alpha data)))]
    (loop [x res, i 0]
      (when-not (> i n)
	(recur (rest x) (inc i))))))

