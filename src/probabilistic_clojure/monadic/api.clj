(ns
    ^{:author "Nils Bertschinger"
      :doc "This library implements a version of the probability monad
which uses Metropolis Hastings sampling.
The system allows to condition and memoize probabilistic choice points and
can be extended by user defined distributions."}
  probabilistic-clojure.monadic.api
  (:use [clojure.contrib.monads :only (defmonad)]
	[probabilistic-clojure.utils.sampling :only (sample-from normalize)]
	[probabilistic-clojure.utils.stuff :only (ensure-list error)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Basic data structures
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord ^{:doc "Basic data structure for random choice points"}
  ChoicePoint
  [sampler get-log-prob proposer get-log-proposal-prob])

(defrecord ^{:doc "Entry holding information about random choices encountered
during a run of probabilistic programs"}
  DBentry
  [value log-lik status type params choice-point])

(defn- activate [database addr]
  (assoc-in database [addr :status] :active))

(defn- inactivate-all [database]
  (into {} (for [[addr entry] database]
	     [addr (assoc entry :status :inactive)])))

(defn- clean-db-back
  "Runs through the database to remove all inactive choice points. Returns the cleaned
database as well as the log-likelihood of the removed choice points which is needed to
calculate the backward probability"
  [database]
  (reduce (fn [[db log-bwd-prob] [addr entry]]
	    (if (= (:status entry) :active)
	      [(assoc db addr entry) log-bwd-prob]
	      [db (+ log-bwd-prob (apply (:get-log-prob (:choice-point entry))
					 (:value entry) (:params entry)))]))
	  [{} 0] (seq database)))

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
    [::invalid log-prob-zero database log-fwd-prob mems]))

(defn invalid? [v]
  (= v ::invalid))

(defn- m-bind-MH [m f]
  (fn [addr database log-fwd-prob log-lik mems]
    ;; here we first run the monad m and then
    ;; plug the values into the continuation f
    ;; (compare the state monad)
    (let [[v log-lik database log-fwd-prob mems]
	  (m (cons "BIND-M" addr) database log-fwd-prob log-lik mems)]
      (if (invalid? v)
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
			;; provide a default proposer that simply samples from the distribution
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
  "Condition a choice point on the specified value.
This function must be applied to an elementary random choice point, e.g. (flip 0.6).
A trace running through this value is then weighted according to the likelihood of the data value."
  [choice val]
  (fn [addr database log-fwd-prob log-lik mems]
    (let [[[_ choice-entry] & more] (seq (get (get-trace choice {}) 2))
	  choice-point (:choice-point choice-entry)
	  ll (apply (:get-log-prob choice-point) val (:params choice-entry))]
      (when more    ; ensure that its was called on an elementary choice point
	(error "Cond-data can only be called on an elementary choice point!"))
      [val (+ log-lik ll) database log-fwd-prob mems])))

(defmacro mem
  "Memoize a MH monadic value on some given arguments, i.e. if the same arguments
are encountered again it refers back to the original choice
point which was established for these arguments in the trace, i.e.
no new randomness is created in this case."
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

;; These two functions are used to select the next choice point to be proposed
;; They implement the heuristics that memoized choices should be tried more often
;; since they got reused several times
(defn select-prob-choice-dist [database mems]
  (normalize
   (into {} (for [[addr entry] database]
	      [[addr entry] (if (contains? mems (rest addr))
			      (mems (rest addr))
			      1)]))))

(defn calc-select-prob [addr database mems]
  (let [total (+ (count database)       ; each entry gets weight one
		 (reduce + (vals mems)) ; weight of mem-entries
		 (- (count mems)))]     ; but got double counted
    (if (contains? mems (rest addr))
      (/ (mems (rest addr)) total)
      (/ 1 total))))
		 
(defn sample-traces
  "The main routine implementing Metropolis Hastings sampling. Returns a lazy
sequence of samples when called on a monadic value from this library.
Burn-in and thinning can be obtained using for example drop and keep-indexed respectively."
  ([m-MH]
     (println "Trying to find valid trace ...")
     (loop [[val log-lik database _fwd-ll_ mems] (get-trace m-MH {})]
       (if (or (invalid? val) (= log-lik log-prob-zero))
	 (recur (get-trace m-MH {}))
	 (do (println "Starting MH-sampling.")
	     (sample-traces m-MH database mems log-lik val 1 1)))))
  ([m-MH database mems log-lik val idx num-acc]
     (when (= (mod idx 500) 0)
       (println (str idx ": value " val " with log. likelihood " log-lik))
       (println (str "Accepted " num-acc " out of last 500 proposals")))
     (let [num-acc (if (= (mod idx 500) 0) 0 num-acc)
	   [addr entry] (sample-from (select-prob-choice-dist database mems))
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
				    (apply (:get-log-prob (:choice-point entry))
					   prop-val (:params entry)))))]
       (if (invalid? next-val) ; trace was rejected => retry
	 (lazy-seq (cons val (sample-traces m-MH database mems log-lik val (inc idx) num-acc)))
	 (let [[next-database log-bwd-prob] (clean-db-back next-database)]
	   (if (< (Math/log (rand))
	   	  (+ (- next-log-lik log-lik)
		     (- (Math/log (calc-select-prob addr next-database next-mems))
			(Math/log (calc-select-prob addr database mems)))
	   	     (- ll-val ll-prop-val)
	   	     (- log-bwd-prob log-fwd-prob)))
	     (lazy-seq (cons next-val (sample-traces m-MH next-database next-mems
						     next-log-lik next-val
						     (inc idx) (inc num-acc))))
	     (lazy-seq (cons val (sample-traces m-MH database mems log-lik val (inc idx) num-acc)))))))))

(defn monte-carlo-samples
  "Run the probabilistic program repeatedly to obtain samples. Note that this is more like
rejection sampling and usually less efficient than sample-traces."
  [m-MH]
  (lazy-seq
   (cons (first (get-trace m-MH {}))
	 (monte-carlo-samples m-MH))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Basic example of how to define a probabilistic choice point
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn flip
  "A binary random choice which is true with probability p.
Provides a good example of how user-defined choice points look like."
  [p]
  (make-choice-point "FLIP" [p]
		     (fn [p] (< (rand) p))  ; the sampling function
		     (fn [b p] (Math/log (if b p (- 1 p)))) ; calculates the log-likelihood of outcome b
		     ;; The proposer (consisting of theses two functions) is optional
		     (fn [b p] (not b))
		     (fn [new-b old-b p] (Math/log 1))))
