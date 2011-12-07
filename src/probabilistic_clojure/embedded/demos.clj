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
  (:use [probabilistic-clojure.embedded.api :only (det-cp gv trace-failure cond-data sample-traces)]
	[probabilistic-clojure.utils.sampling :only (sample-from normalize density)]
	[probabilistic-clojure.embedded.choice-points
	 :only (flip-cp gaussian-cp dirichlet-cp log-pdf-dirichlet discrete-cp log-pdf-discrete dirichlet-process)]

	[incanter.core   :only (view)]
	[incanter.charts :only (histogram add-lines xy-plot)]
	[incanter.stats  :only (sample-normal sample-dirichlet pdf-normal mean)]))

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
   (take 7500 (drop 500 (sample-traces model)))))

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
    (loop [points data
	   idx 0]
      (when (seq points)
	(let [comp (discrete-cp [:comp idx] (zipmap comp-labels (gv comp-weights)))]
	  ;;     mu-comp (det-cp [:mu-comp idx] (gv (get comp-mus (gv comp))))]
	  ;; (cond-data (gaussian-cp [:mu idx] (gv mu-comp) 1.0) (first points))
	  (cond-data (gaussian-cp [:mu idx] (gv (get comp-mus (gv comp))) 1.0) (first points))
	  (recur (rest points)
		 (inc idx)))))
    (det-cp :mixture
      [(into {} (for [[comp mu] comp-mus] [comp (gv mu)]))
       (gv comp-weights)])))

(defn transpose
  "Transpose a list of lists, i.e. (transpose [[1 2] [3 4] [5 6]]) = ((1 3 5) (2 4 6))"
  [lls]
  (apply map list lls))

(defn test-mixture [comp-labels model]
  (let [data-plot (histogram data :title "Dataset" :nbins 50 :density true)
	samples  (take 200 (drop 7500 (sample-traces (fn [] (model comp-labels data)))))
	comp-mus (map first samples)
	comp-weights (map second samples)]
    (let [xs (range -10 10 0.01)
	  weights (map mean (transpose comp-weights))
	  mus (map mean (transpose (for [mus comp-mus] [(:a mus) (:b mus) (:c mus)])))]
      (doto data-plot
	(add-lines xs (map (fn [x] (* (nth weights 0) (pdf-normal x :mean (nth mus 0)))) xs))
	(add-lines xs (map (fn [x] (* (nth weights 1) (pdf-normal x :mean (nth mus 1)))) xs))
	(add-lines xs (map (fn [x] (* (nth weights 2) (pdf-normal x :mean (nth mus 2)))) xs))
	view)
      [weights mus])))

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
		   ;; (println (inc idx) ": " mu)
		   [(count comp-mus) comp-mus]))))
      comps)))

(defn test-DP [alpha n]
  (let [res (sample-traces (fn [] (mixture-DP alpha data)))]
    (loop [x res, i 0]
      (when (not (> i n))
	(when (= (mod i 2500) 0)
	  (print (first x)))
	(recur (rest x) (inc i))))))

