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

(ns probabilistic.demos
  (:use probabilistic.metropolis-hastings)
  (:use [clojure.contrib.monads :only (domonad m-bind m-result with-monad)])
  (:use [incanter.core :only (view)]
	[incanter.stats :only (sample-normal pdf-normal mean sample-beta pdf-beta)]
	[incanter.charts :only (histogram xy-plot add-lines)]))

(in-ns 'probabilistic.demos)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; First a simple Bayes net as found in many introductory texts
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn noisy-or [x y]
  (domonad probabilistic-sampling-m
   [noise-x (flip 0.9)
    noise-y (flip 0.8)
    noise-z (flip 0.1)]
   (or (and x noise-x)
       (and y noise-y)
       noise-z)))

(defn grass-bayes-net []
  (domonad probabilistic-sampling-m
   [rain      (flip 0.3)
    sprinkler (flip 0.5)
    grass-is-wet (noisy-or rain sprinkler)
    :when grass-is-wet]
   rain))

(defn density [samples]
  (let [freqs (frequencies samples)
	total (reduce + (vals freqs))]
    (into {} (for [[k v] freqs] [k (float (/ v total))]))))

(density (take 10000 (sample-traces (grass-bayes-net))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Fitting of a mixture model to illustrate how mem can be used to share randomness
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn generate-data []
  (let [mu (fn [] (sample-from {-5 0.2, 0 0.7, 8 0.1}))]
    (lazy-seq (cons (sample-normal 1 :mean (mu))
		    (generate-data)))))

(def data (take 42 (generate-data)))

(defn fit-components [data comp-weights mu-comps]
  (with-monad probabilistic-sampling-m
    (if (empty? data)
      (m-result ())
      (domonad
       [comp (discrete {:a (nth comp-weights 0), :b (nth comp-weights 1), :c (nth comp-weights 2)})
	:let [mu-comp (mu-comps comp)]
	obs  (cond-data (gaussian mu-comp 1) (first data))
	assignment (fit-components (rest data) comp-weights mu-comps)]
       (cons comp assignment)))))

(defn mixture [data]
  (domonad probabilistic-sampling-m
    [ca (gaussian 0 15)
     cb (gaussian 0 15)
     cc (gaussian 0 15)
     comp-weights (dirichlet [1 1 1])
     :let [mu-comps {:a ca :b cb :c cc}]
     assignment (fit-components data comp-weights mu-comps)]
    [mu-comps comp-weights assignment]))

(defn mixture-mem [data]
  (with-monad probabilistic-sampling-m
    (if (empty? data)
      (m-result [{} [] ()])
      (domonad
       [comp-weights (mem (dirichlet [10 10 10]))
	comp (discrete {:a (nth comp-weights 0), :b (nth comp-weights 1), :c (nth comp-weights 2)})
	mu-comp (mem (gaussian 0 15) comp)
	obs (cond-data (gaussian mu-comp 1) (first data))
	[other-mus cws assignment] (mixture-mem (rest data))]
       [(assoc other-mus comp mu-comp) comp-weights (cons comp assignment)]))))

(defn transpose
  "Transpose a list of lists, i.e. (transpose [[1 2] [3 4] [5 6]]) = ((1 3 5) (2 4 6))"
  [lls]
  (apply map list lls))

(defn test-mixture [model]
  (let [data-plot (histogram data :title "Dataset" :nbins 50 :density true)
	samples  (take 2000 (drop 8000 (sample-traces (model data))))
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
;;; Finally, extend this to a Dirichlet process such that also the number of
;;; components is learned
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn beta [alpha beta]
  (make-choice-point "BETA" [alpha beta]
		     (fn [alpha beta] (sample-beta 1 :alpha alpha :beta beta))
		     (fn [x alpha beta] (Math/log (pdf-beta x :alpha alpha :beta beta)))))

(defn pick-a-stick [alpha idx]
  (domonad probabilistic-sampling-m
    [stick (mem (beta 1 alpha) idx)
     stop  (flip stick)
     num (if stop
	   (m-result idx)
	   (pick-a-stick alpha (inc idx)))]
    num))

(defn dirichlet-process [alpha base]
  (domonad probabilistic-sampling-m
    [idx (pick-a-stick alpha 1)
     val (mem base idx)]
    val))

(defn mixture-DP [alpha data]
  (with-monad probabilistic-sampling-m
    (if (empty? data)
      (m-result [0 {} ()])
      (domonad
       [mu-comp (dirichlet-process alpha (gaussian 0 15))
	obs (cond-data (gaussian mu-comp 1) (first data))
	[num-comp comp-mus assignment] (mixture-DP alpha (rest data))]
       (let [comp-idx (if (contains? comp-mus mu-comp)
			(comp-mus mu-comp)
			(inc num-comp))
	     comp-mus (assoc comp-mus mu-comp comp-idx)]
	 [(count comp-mus) comp-mus (cons comp-idx assignment)])))))

(defn plot-DP-fit [data res]
  (let [data-plot (histogram data :nbins 50 :density true)
	[num-comp mus assignment] res
	weights (density assignment)
	xs (range -15 15 0.01)]
    (doseq [[mu idx] (seq mus)]
      (add-lines data-plot xs (map (fn [x] (* (weights idx) (pdf-normal x :mean mu))) xs)))
    (add-lines data-plot xs (map (fn [x] (reduce + (for [[mu idx] (seq mus)]
						     (* (weights idx) (pdf-normal x :mean mu)))))
				 xs))
    (view data-plot)))

(defn test-DP [alpha n]
  (let [res (sample-traces (mixture-DP alpha data))]
    (loop [x res, i 0]
      (when (not (> i n))
	(when (= (mod i 2500) 0)
	  (plot-DP-fit data (first x)))
	(recur (rest x) (inc i))))))