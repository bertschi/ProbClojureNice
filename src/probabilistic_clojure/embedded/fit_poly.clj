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
  (:use [probabilistic-clojure.embedded.api :only (det-cp gv cond-data metropolis-hastings-sampling def-prob-cp)]
	[probabilistic-clojure.utils.stuff :only (indexed)]
	[probabilistic-clojure.utils.sampling :only (density)]
	[probabilistic-clojure.embedded.choice-points
	 :only (gaussian-cp discrete-cp *gaussian-proposal-sdev*)]

	[incanter.core   :only (view)]
	[incanter.charts :only (histogram add-lines xy-plot scatter-plot)]
	[incanter.stats  :only (sample-normal pdf-normal)]))

(in-ns 'probabilistic-clojure.embedded.fit-poly)

(defn poly-ranked
  "Evaluate the polynomial with the given coefficients at x:
f(x) = coeffs[0] + coeffs[1]*x + ... + coeffs[k]*x^(k-1)"
  [x coeffs]

  (reduce + (map * coeffs (iterate (partial * x) 1))))

(defn poly-horner
  "Evaluate the polynomial with the given coefficients at x. 
Evaluation follows the Horner scheme: 
f(x) = coeffs[0] + x*(coeffs[1] + ... + x*(coeffs[k])...)" 
  [x coeffs]

  (reduce (fn [y c]
	      (+ c (* x y)))
	  (reverse coeffs)))

(defn poly-roots
  [x [scale & roots]]
  (* scale 
     (reduce * (map #(- x %) roots))))

(defn ^:dynamic legendre-basis [n x]
  (cond (= n 0) 1
	(= n 1) x
	:else (let [n- (dec n)]
		(/ (- (* (+ (* 2 n-) 1) x (legendre-basis n- x))
		      (* n- (legendre-basis (dec n-) x)))
		   n))))

(defn poly-legendre [x coeffs]
  (binding [legendre-basis (memoize legendre-basis)]
    (let [x (/ x 4)]
      (reduce +
	      (for [[i c] (indexed coeffs)]
		(* c (legendre-basis i x)))))))

(def poly poly-legendre)

(def test-poly [-1 1 -0.7 0.3])

(defn uni-rand [low high]
  (+ low (rand (- high low))))

(def demo-data
     (repeatedly 17
		 (fn []
		   (let [x (uni-rand -5 5)
			 y (poly-ranked x test-poly)]
		     [x (sample-normal 1 :mean y :sd 2)]))))

;; special gaussian-cp which initially returns mu
(def-prob-cp gaussian0-cp [mu sdev]
  :sampler [] (sample-normal 1 :mean 0 :sd 0.1) ;; mu
  :calc-log-lik [x] (Math/log (pdf-normal x :mean mu :sd sdev))
  :proposer [old-x] (let [proposal-sd *gaussian-proposal-sdev*
			  new-x (sample-normal 1 :mean old-x :sd proposal-sd)]
		      [new-x
		       (Math/log (pdf-normal new-x :mean old-x :sd proposal-sd))
		       (Math/log (pdf-normal old-x :mean new-x :sd proposal-sd))]))

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
	   				   (gv (gaussian0-cp [:coeff rank r]
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

(defn poly-fit-shared
  ([data] (poly-fit-shared [1] data))
  ([rank-range data]
     (let [n (count rank-range)
	   rank (if (= n 1)
		  (det-cp :rank (first rank-range))
		  (discrete-cp :rank (zipmap rank-range (repeat (/ 1 n)))))
	   coeffs (det-cp :coeffs
			  ;; one set of coeffs which are shared by all models
			  ;; and removed if unused
			  (doall
			   (for [r (range (inc (gv rank)))]
			     (gv (gaussian0-cp [:coeff r]
					       0.0 5.0)))))
	   obs-noise (det-cp :noise
			     (Math/abs (gv (gaussian-cp [:noise rank]
							0.0 5.0))))]
       (doseq [[i [x y]] (indexed data)]
	 (cond-data (gaussian-cp [:obs i]
				 (poly x (gv coeffs))
				 (gv obs-noise))
		    y))
       (det-cp :fit
	       [(gv rank) (gv coeffs) (gv obs-noise)]))))

(defn poly-demo-shared [ranks data]
  (let [xs (range -5 5 0.05)

	samples (take 75000 (metropolis-hastings-sampling
			     (fn [] (poly-fit-shared ranks demo-data))))
	fitted (last samples)
	graph (scatter-plot (map first demo-data) (map second demo-data))]
    (println (density (map first samples)))
    (doseq [r ranks]
      (add-lines graph xs (map #(poly % (take r (second fitted))) xs)))
    (view graph)))
