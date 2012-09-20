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

(ns
    ^{:author "Nils Bertschinger"
      :doc "Part of probabilistic programming for Clojure.

Experimental support for simulated annealing as well as annealed
importance sampling. Basically, refactors the core sampling routine to
get a handle on the acceptance condition and allow for interrupting
and restarting sampling."}
  probabilistic-clojure.embedded.anneal
  (:use [clojure.set :only (union)])
  (:use probabilistic-clojure.embedded.api))

(in-ns 'probabilistic-clojure.embedded.anneal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; New interface to the sampler
;;;
;;; More flexible, easy to support different sampling strategies
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn metropolis-hastings-stepper [choice-points selected selection-dist acceptor]
  (with-fresh-store choice-points
    (let [selected-cp (choice-points selected)
	  
	  [prop-val fwd-log-lik bwd-log-lik]
	  (propose selected-cp (:value selected-cp))]
      ;; Propose a new value for the selected choice point and propagate change to dependents
      (set-proposed-val! (:name selected-cp) prop-val)
      (let [updates (propagate-change-to (:dependents selected-cp))]
	;; (println "Proposed " (:name selected-cp) " for " updates " updates ("
	;; 	 (count-all-dependents (:name selected-cp) choice-points) " dependents)"))
	)
	
      (if (trace-failed?)
	[choice-points ::rejected true selection-dist]
	(let [removed-cps (remove-uncalled-choices)
	      same-topology (and (empty? (fetch-store :newly-created))
				 (empty? removed-cps))
	      ;; Here we have the following invariants:
	      ;; * (assert (empty? (clojure.set/intersection removed-cps (fetch-store :newly-created))))
	      ;; * (let [new (set (keys (fetch-store :choice-points)))
	      ;; 	 old (set (keys choice-points))]
	      ;;     (assert (and (= new (difference (union old (fetch-store :newly-created))
	      ;;  				     removed-cps))
	      ;; 		  (= old (difference (union new removed-cps) (fetch-store :newly-created))))))

	      ;; Overall the recomputed and removed-cps were touched during the update
	      ;; Thus, we have to calculate the total probability contributed to the old
	      ;; as well as the new traces.
	      touched-cps (union (fetch-store :recomputed) removed-cps)
	      trace-log-lik (total-log-lik touched-cps choice-points)
	      prop-trace-log-lik (total-log-lik touched-cps (fetch-store :choice-points))

	      ;; The forward and backward probabilities now account for the newly-created
	      ;; and removed choice points
	      fwd-trace-log-lik (total-log-lik (fetch-store :newly-created) (fetch-store :choice-points))
	      bwd-trace-log-lik (total-log-lik removed-cps choice-points)

	      prop-selection-dist (if same-topology
				    selection-dist
				    ;; (prob-choice-dist (fetch-store :choice-points)))]
				    (-> selection-dist
				    	(add-to-prob-choice-dist (fetch-store :newly-created)
				    				 (fetch-store :choice-points))
				    	(remove-from-prob-choice-dist removed-cps)))]
	  ;; Randomly accept the new proposal according to the Metropolis Hastings formula
	  (if (acceptor prop-trace-log-lik
			trace-log-lik
			;; the total forward proposal probability
			(+ (Math/log (prob selection-dist (:name selected-cp)))
			   fwd-trace-log-lik
			   fwd-log-lik)
			;; and the backward probability
			(+ (Math/log (prob prop-selection-dist (:name selected-cp)))
			   bwd-trace-log-lik
			   bwd-log-lik))
	      ;; (< (Math/log (rand))
	      ;; 	 (+ (- prop-trace-log-lik trace-log-lik)
	      ;; 	    (- (Math/log (prob prop-selection-dist (:name selected-cp)))
	      ;; 	       (Math/log (prob selection-dist (:name selected-cp))))
	      ;; 	    (- bwd-trace-log-lik fwd-trace-log-lik)
	      ;; 	    (- bwd-log-lik fwd-log-lik)))
	    [(fetch-store :choice-points) ::accepted same-topology prop-selection-dist]
	    [choice-points ::rejected true selection-dist]))))))

;; The sampler core has to change as well:
;; * The acceptor can be specified from the outside

;; * To allow for interrupting and restarting of sampling the
;;   choice-points are passed in from the outside and returned
;;   alongside each sample which is now of the form
;;     {:value val :choice-points choice-points}
(defn metropolis-hastings-sampling-core [[cp choice-points] acceptor]
  (letfn [(samples [choice-points idx num-accepted num-top-changed update-seq selection-dist]
	    (lazy-seq
	     (let [update-seq (or (seq update-seq)
				  (new-update-sequence (prob-choice-dist choice-points)))
		   val (cp-value cp choice-points)
		   
		   [next-choice-points status same-topology next-selection-dist]
		   (metropolis-hastings-stepper choice-points (first update-seq) selection-dist acceptor)
		   
		   output-info false] ;; (= (mod idx *info-steps*) 0)]
	       (when output-info
		 (println idx ": " val)
		 (println "Log. lik.: " (total-log-lik (keys choice-points) choice-points))
		 (println "Accepted " num-accepted " out of last " *info-steps* " samples.")
		 (println "Topology changed on " num-top-changed " samples."))
	       (cons {:value val :choice-points choice-points}
		     (samples next-choice-points
			      (inc idx)
			      (cond output-info 0
				    (= status ::accepted) (inc num-accepted)
				    :else num-accepted)
			      (cond output-info 0
				    (not same-topology) (inc num-top-changed)
				    :else num-top-changed)
			      (if same-topology
				(rest update-seq)
				(new-update-sequence next-selection-dist))
			      next-selection-dist)))))]
    (let [selection-dist (prob-choice-dist choice-points)]
      (samples choice-points 0 0 0 (new-update-sequence selection-dist) selection-dist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; This shows how the standard sampling procedure can be obtained
;;; using the new interface to the sampler
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn metropolis-hastings-acceptor
  [prop-trace-log-lik trace-log-lik total-fwd-log-lik total-bwd-log-lik]
  (< (Math/log (rand))
     (+ (- prop-trace-log-lik trace-log-lik)
	(- total-bwd-log-lik total-fwd-log-lik))))

(defn standard-metropolis-hastings-sampling
  ([prob-thunk]
     (standard-metropolis-hastings-sampling prob-thunk
					    metropolis-hastings-acceptor))
  ([prob-thunk acceptor]
     (println "Trying to find a valid trace ...")
     (let [cp-and-choice-points (find-valid-trace prob-thunk)]
       (println "Started sampling")
       (map :value
	    (metropolis-hastings-sampling-core cp-and-choice-points
					       acceptor)))))

;; test this on the demo code
;;
;; (probabilistic-clojure.utils.sampling/density
;;  (take 7500
;;        (drop 500
;; 	     (standard-metropolis-hastings-sampling
;; 	      probabilistic-clojure.embedded.demos/grass-bayes-net))))

;; (last
;;  (take 7500
;;        (standard-metropolis-hastings-sampling
;; 	(fn [] (probabilistic-clojure.embedded.demos/mixture-memo 
;; 		[:a :b :c]
;; 		probabilistic-clojure.embedded.demos/data)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Simulated annealing ... simple plug in a different acceptor
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn simulated-annealing-acceptor [inv-temperature]
  (fn [prop-trace-log-lik trace-log-lik total-fwd-log-lik total-bwd-log-lik]
    ;; ignores the forward-backward probability and accepts according
    ;; to the scaled (with the inverse temperature) likelihood
    ;; difference
    (< (Math/log (rand))
       (* inv-temperature
	  (- prop-trace-log-lik trace-log-lik)))))

(defn simulated-annealing
  "Implements simulated annealing. The temperature schedule is a
  sequence containing [inv-temperature number-of-steps] pairs.

  Usually one wants to start with a rather low inverse temperature and
  increase it over time."
  [prob-thunk inv-temperature-schedule]

  (println "Trying to find a valid trace ...")
  (let [[cp choice-points] (find-valid-trace prob-thunk)]
    (println "Started sampling")
    (reduce concat
	    (first
	     (reduce (fn [[samples choice-points] [inv-temperature steps]]
		       (let [more-samples
			     (take steps (metropolis-hastings-sampling-core
					  [cp choice-points]
					  (simulated-annealing-acceptor inv-temperature)))]
			 [(conj samples (map :value more-samples))
			  (:choice-points (last more-samples))]))
		     [[] choice-points]
		     inv-temperature-schedule)))))

;; This nicely optimizes the Gaussian mixture model
;; (last
;;  (simulated-annealing
;;   (fn [] (probabilistic-clojure.embedded.demos/mixture-memo 
;; 	  [:a :b :c] probabilistic-clojure.embedded.demos/data))
;;   [[0.01 2500] [0.1 2500] [1 2500] [10 2500] [100 2500]]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Annealed importance sampling
;;;
;;; TODO: Distinguish between conditioned and unconditioned choice
;;;       points to handle prior and likelihood weights differently!
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn annealed-importance-acceptor
  "One way to obtain a sequence of chains for annealed importance
  sampling. Uses the Metropolis-Hastings acceptance condition, but
  mixes for the distribution p(x)^beta instead of p(x)."
  [beta]
  (fn [prop-trace-log-lik trace-log-lik total-fwd-log-lik total-bwd-log-lik]
    (< (Math/log (rand))
       (+ (* beta (- prop-trace-log-lik trace-log-lik))
	  (- total-bwd-log-lik total-fwd-log-lik)))))

(defn annealed-importance-sample
  "Implements annealed importance sampling to draw ONE sample with its
  corresponding importance weight. For the sample a sequence of
  Markov-chains according to the given annealing schedule (sequence of
  [beta num-steps] pairs) is run and used to calculate its importance
  weight. Beta should start close to zero and then slowly increase
  towards 1.

  Running this function repeatedly produces independent, weighted
  samples from the distribution specified by the probabilistic
  function prob-thunk. The variance of the importance weights can be
  used as diagnostic for the quality of the obtained samples which
  depends on how well the Markov chains are mixing."
  [prob-thunk annealing-schedule]

  (let [[cp choice-points] (find-valid-trace prob-thunk)]
    (print "Sampling ... ")
    (let [[x-0 log-weights choice-points]
	  (reduce (fn [[x-n-1 log-ws choice-points] [beta-n-1 steps-T-n-1]]
		    (let [prob-x-n-1 (* beta-n-1 (total-log-lik (keys choice-points) choice-points))
			  {x-n-2 :value new-choice-points :choice-points}
			  (last (take steps-T-n-1
				      (metropolis-hastings-sampling-core
				       [cp choice-points]
				       (annealed-importance-acceptor beta-n-1))))
			  prob-x-n-2 (* beta-n-1 (total-log-lik (keys new-choice-points)
								new-choice-points))]
		      ;; (println "Chain moved " x-n-1 " to " x-n-2)
		      ;; (println "Log. weight difference: " (- prob-x-n-1 prob-x-n-2))
		      [x-n-2
		       (conj log-ws (- prob-x-n-1 prob-x-n-2))
		       new-choice-points]))
		  [(cp-value cp choice-points)
		   (let [uncond-cps (filter (fn [cp] (not (:conditioned? cp))) (vals choice-points))
			 prior-log-lik (total-log-lik (map :name uncond-cps) choice-points)]
		     [(- prior-log-lik)])
		   choice-points]
		  annealing-schedule)
	  prob-x-0 (total-log-lik (keys choice-points) choice-points)]
      (println "value: " x-0 " with weight: " (+ prob-x-0 (reduce + log-weights)))
      {:value x-0
       :log-importance-weight (+ prob-x-0 (reduce + log-weights))
       :debug (conj log-weights prob-x-0)})))

;; Try this on a very simple model, i.e. fitting the mean of a
;; standard Gaussian with a Gaussian prior

(use '[probabilistic-clojure.embedded.choice-points :only (gaussian-cp)])
(use '[probabilistic-clojure.utils.stuff :only (indexed)])
(use '[incanter.stats :only (sample-normal pdf-normal)])

(defn gauss-fit [mu-prior sd-prior sd-likelihood data]
  (let [mu (gaussian-cp :mu mu-prior sd-prior)]
    (doseq [[i x] (indexed data)]
      (cond-data (gaussian-cp [:obs i] (gv mu) sd-likelihood)
		 x))
    (det-cp :fit (gv mu))))

(def xs (sample-normal 10 :mean 2.5 :sd 1))

;; The theoretical posterior and marginal likelihood for the Gaussian
;; mean fit Formulas are from notes by Kevin Murphy ... simplify by
;; using precision (lambda) instead of variance

(defn posterior [mu-0 lambda-0 lambda xs]
  (let [lambda-n (+ lambda-0 (* (count xs) lambda))
        mu-n     (/ (+ (* lambda (reduce + xs))
                       (* lambda-0 mu-0))
                    lambda-n)]
    {:mu mu-n :sdev (Math/sqrt (/ 1 lambda-n))}))

(defn log-marginal-likelihood [mu-0 lambda-0 lambda xs]
  ;; formula (42) from the notes
  (let [sig (Math/sqrt (/ 1 lambda))
        n-*-x-mean (reduce + xs)
        n (count xs)]
    (+ (Math/log (/ sig (* (Math/pow (* (Math/sqrt (* 2 Math/PI)) sig) n)
                           (Math/sqrt (+ (* n (/ 1 lambda-0)) (/ 1 lambda))))))
       (- (+ (/ (reduce + (map * xs xs)) (* 2 (/ 1 lambda)))
             (/ (* mu-0 mu-0) (* 2 (/ 1 lambda-0)))))
       (/ (+ (/ (* (/ 1 lambda-0) n-*-x-mean n-*-x-mean)
                (/ 1 lambda))
             (/ (* (/ 1 lambda) mu-0 mu-0)
                (/ 1 lambda-0))
             (* 2 n-*-x-mean mu-0))
          (* 2 (+ (* n (/ 1 lambda-0)) (/ 1 lambda)))))))
  
;; TODO: check this formula ... seems to use improper flat prior!!!

;; The empirical average of the importance weights should be close to that!

(use '[incanter.core :only (view)])
(use '[incanter.charts :only (histogram add-lines)])

(use '[probabilistic-clojure.utils.sampling :only (sample-from normalize density)])

(defn resampling-distribution [importance-samples]
  (let [max-log-weight (reduce max (map :log-importance-weight importance-samples))]
    (normalize
     (into {} (for [sample importance-samples]
                [(:value sample)
                 (Math/exp (- (:log-importance-weight sample) max-log-weight))])))))

(defn log-sum-exp
  "Evaluates \\log \\sum_i e^{x_i}."
  [xs]
  (let [x-max (apply max xs)]
    (+ x-max
       (Math/log (sum (map #(Math/exp (- % x-max)) xs))))))

(defn effective-size
  "Calculates the effective sample size for the given importance weights:
    N_{eff} = \\frac{(\\sum_i w_i)^2}{\\sum w_i^2}
  "
  [importance-weights]
  (Math/exp (- (* 2 (log-sum-exp importance-weights))
               (log-sum-exp (map (partial * 2) importance-weights)))))
  
(defn test-ais [xs num-samples]
  (let [mu-prior      0
        sd-prior      10
	sd-likelihood 1
        lambda-0      (/ 1 (* sd-prior sd-prior))
        lambda        (/ 1 (* sd-likelihood sd-likelihood))

        {mu-n :mu sd-n :sdev} (posterior mu-prior lambda-0 lambda xs)
        
	a-schedule (for [beta (range 0.05 0.95 0.05)]
		     [beta 100])
	samples
	(repeatedly num-samples
		    (fn [] (annealed-importance-sample (fn [] (gauss-fit mu-prior sd-prior sd-likelihood xs)) a-schedule)))]
    (println "Posterior: mu = " mu-n ", sdev = " sd-n)
    (println "Log. marginal likelihood of data: " (log-marginal-likelihood mu-prior lambda-0 lambda xs))
    (println "Log. average importance weights:  "
             (- (log-sum-exp (map :log-importance-weight samples))
                (Math/log (count samples))))
    (println "Effective sample size: " (effective-size (map :log-importance-weight samples)))
    (let [dist (resampling-distribution samples)
          hist (histogram (repeatedly 250 (fn [] (sample-from dist)))
                          :nbins 50 :density true)
          x-range (range -5 5 0.01)]
      (doto hist
        (add-lines x-range (map (fn [x] (pdf-normal x :mean mu-n :sd sd-n)) x-range))
        view))))

(defn test-MH [xs num-samples]
  (let [mu-prior      0
        sd-prior      10
	sd-likelihood 1
        lambda-0      (/ 1 (* sd-prior sd-prior))
        lambda        (/ 1 (* sd-likelihood sd-likelihood))

        {mu-n :mu sd-n :sdev} (posterior mu-prior lambda-0 lambda xs)

        samples (take num-samples
                      (drop 2500
                            (standard-metropolis-hastings-sampling
                             (fn [] (gauss-fit mu-prior sd-prior sd-likelihood xs)))))

        hist (histogram (repeatedly 250 (fn [] (sample-from (density samples))))
                        :nbins 50 :density true)
        x-range (range -5 5 0.01)]
    (doto hist
      (add-lines x-range (map (fn [x] (pdf-normal x :mean mu-n :sd sd-n)) x-range))
      view)))
