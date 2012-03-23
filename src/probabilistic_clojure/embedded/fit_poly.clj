;;; Copyright (C) 2012 Nils Bertschinger

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
      :doc "Part of probabilistic-clojure.embedded. Demo of fitting polynomials."}
  probabilistic-clojure.embedded.fit-poly
  (:use [probabilistic-clojure.embedded.api :only (det-cp gv trace-failure cond-data metropolis-hastings-sampling)]
	[probabilistic-clojure.utils.stuff :only (indexed)]
	[probabilistic-clojure.utils.sampling :only (normalize sample-from)]
	[probabilistic-clojure.embedded.choice-points
	 :only (gaussian-cp discrete-cp log-pdf-discrete)]

	[incanter.core   :only (view)]
	[incanter.charts :only (histogram add-lines xy-plot scatter-plot)]
	[incanter.stats  :only (sample-normal pdf-normal)]))

(in-ns 'probabilistic-clojure.embedded.fit-poly)

(defn poly
  "Evaluate the polynomial with the given coefficients at x:
f(x) = coeffs[0] + coeffs[1]*x + ... + coeffs[k]*x^(k-1)"
  [x coeffs]

  (reduce + (map * coeffs (iterate (partial * x) 1))))

(def test-poly [-1 1 0.5 -0.2])

(defn uni-rand [low high]
  (+ low (rand (- high low))))

(def demo-data
     (repeatedly 42
		 (fn []
		   (let [x (uni-rand -5 5)
			 y (poly x test-poly)]
		     [x (sample-normal 1 :mean y :sd 0.5)]))))

(defn poly-fit-fixed
  [rank data]
  (let [coeffs (det-cp :coeffs
		       (doall
			(for [r (range (inc rank))]
			  (gv (gaussian-cp [:coeff r]
					   0.0 5.0)))))]
    (doseq [[i [x y]] (indexed data)]
      (let [mu (det-cp [:mu i] (poly x (gv coeffs)))]
	(cond-data (gaussian-cp [:obs i]
				(gv mu)
				1.0)
		 y)))
    (det-cp :fit
	    (gv coeffs))))

(defn poly-fit
  ([data] (poly-fit [1] data))
  ([rank-range data]
     (let [n (count rank-range)
	   rank (if (= n 1)
		  (det-cp :rank (first rank-range))
		  (discrete-cp :rank (zipmap rank-range (repeat (/ 1 n)))))
	   coeffs (det-cp :coeffs
	   		  (into {}
	   			(for [rank rank-range]
	   			  [rank (doall
	   				 (for [r (range (inc rank))]
	   				   (gv (gaussian-cp [:coeff rank r]
	   						    0.0 5.0))))])))
	   obs-noise (det-cp :noise
	   		     (into {} (for [rank rank-range]
	   				[rank (Math/abs (gv (gaussian-cp [:noise rank]
									 0.0 5.0)))])))]
       (doseq [[i [x y]] (indexed data)]
	 (cond-data (gaussian-cp [:obs i]
				 (poly x (get (gv coeffs) (gv rank)))
				 (get (gv obs-noise) (gv rank)))
		    y))
       (det-cp :fit
	       [(gv rank) (gv coeffs) (gv obs-noise)]))))

(defn poly-demo [ranks data]
  (let [xs (range -5 5 0.05)

	fitted (last (take 7500 (metropolis-hastings-sampling
				 (fn [] (poly-fit ranks demo-data)))))
	graph (scatter-plot (map first demo-data) (map second demo-data))]
    (doseq [r ranks]
      (add-lines graph xs (map #(poly % (get (second fitted) r)) xs)))
    (view graph)))