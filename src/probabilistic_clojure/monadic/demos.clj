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
      :doc "Demo of how the probability monad can be used.
Also defines several useful probabilistic choice points and
requires incanter for different distributions as well as the
graphical output."}
  probabilistic-clojure.monadic.demos
  (:use [probabilistic-clojure.monadic.api
	 :only (probabilistic-sampling-m make-choice-point cond-data mem sample-traces flip log-prob-zero)]
	[probabilistic-clojure.utils.sampling :only (density sample-from)]
	[probabilistic-clojure.utils.stuff :only (transpose)])
  (:use [clojure.algo.monads :only (domonad m-bind m-result with-monad)])
  (:use [incanter.core :only (gamma view)]
	[incanter.stats :only (sample-normal pdf-normal sample-dirichlet sample-beta pdf-beta mean)]
	[incanter.charts :only (histogram xy-plot add-lines)]))

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

(defn run-grass-example [num-samples]
  (let [rain (density (take num-samples (sample-traces (grass-bayes-net))))]
    (println "Given grass-is-wet the probability for rain is " (get rain true))
    rain))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Some more probabilistic choice points as required by the mixture example
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
			 (Math/log (pdf-normal new-x :mean old-x :sd proposal-sd))))))

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
    (if (empty? data) ; are we done yet?
      (m-result ())
      (domonad
       [comp (discrete {:a (nth comp-weights 0), :b (nth comp-weights 1), :c (nth comp-weights 2)})
	;; first draw a component for this data point
	:let [mu-comp (mu-comps comp)]
	;; then condition a Gaussian for this component on the observed data point
	obs  (cond-data (gaussian mu-comp 1) (first data))
	assignment (fit-components (rest data) comp-weights mu-comps)]
       (cons comp assignment)))))

(defn mixture
  "Basic example of a mixture model."
  [data]
  (domonad probabilistic-sampling-m
    [ca (gaussian 0 15) ; draw means of three components from a Gaussian prior
     cb (gaussian 0 15)
     cc (gaussian 0 15)
     comp-weights (dirichlet [1 1 1]) ; draw component proportions from a Dirichlet prior
     :let [mu-comps {:a ca :b cb :c cc}]
     assignment (fit-components data comp-weights mu-comps)] ; assign each data point to these components
    [mu-comps comp-weights assignment]))

(defn mixture-mem
  "The same model as in mixture, but simplified using mem to reuse random choices."
  [data]
  (with-monad probabilistic-sampling-m
    (if (empty? data)
      (m-result [{} [] ()])
      (domonad
       [comp-weights (mem (dirichlet [10 10 10])) ; mem ensures that the component proportions
	                                          ; are the same for each data point
	comp (discrete {:a (nth comp-weights 0), :b (nth comp-weights 1), :c (nth comp-weights 2)})
	mu-comp (mem (gaussian 0 15) comp) ; similarly the means of the same component are shared
	obs (cond-data (gaussian mu-comp 1) (first data)) ; condition on the observed data
	[other-mus cws assignment] (mixture-mem (rest data))]
       [(assoc other-mus comp mu-comp) comp-weights (cons comp assignment)]))))

(defn test-mixture [model]
  (let [data-plot (histogram data :title "Dataset" :nbins 50 :density true)
	samples  (take 200 (drop 8000 (sample-traces (model data)))) ; burn-in of 8000 samples
	comp-mus (map first samples)
	comp-weights (map second samples)]
    (let [xs (range -10 10 0.01)
	  ;; average over the last samples ... even though this should not be done!!!
	  weights (map mean (transpose comp-weights))
	  mus (map mean (transpose (for [mus comp-mus] [(:a mus) (:b mus) (:c mus)])))]
      (doto data-plot
	(add-lines xs (map (fn [x] (* (nth weights 0) (pdf-normal x :mean (nth mus 0)))) xs))
	(add-lines xs (map (fn [x] (* (nth weights 1) (pdf-normal x :mean (nth mus 1)))) xs))
	(add-lines xs (map (fn [x] (* (nth weights 2) (pdf-normal x :mean (nth mus 2)))) xs))
	view)
      [weights mus])))

(comment
  (test-mixture mixture)
  (test-mixture mixture-mem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Finally, extend this to a Dirichlet process such that also the number of
;;; components is learned
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; first a Beta distributed choice point is needed
(defn beta [alpha beta]
  (make-choice-point "BETA" [alpha beta]
		     (fn [alpha beta] (sample-beta 1 :alpha alpha :beta beta))
		     (fn [x alpha beta] (Math/log (pdf-beta x :alpha alpha :beta beta)))))

;; this implements the stick breaking construction
;; note the use of mem to reuse randomness
(defn pick-a-stick [alpha idx]
  (domonad probabilistic-sampling-m
    [stick (mem (beta 1 alpha) idx)
     stop  (flip stick)
     num (if stop
	   (m-result idx)
	   (pick-a-stick alpha (inc idx)))]
    num))

(defn dirichlet-process
  "A Dirichlet process with parameter alpha and base measure base."
  [alpha base]
  (domonad probabilistic-sampling-m
    [idx (pick-a-stick alpha 1)
     val (mem base idx)]
    val))

(defn mixture-DP
  "A Gaussian Dirichlet process mixture model."
  [alpha data]
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

(comment
  (test-DP 1.0 7500))
