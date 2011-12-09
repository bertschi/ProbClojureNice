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
      :doc "This library implements probabilistic programming for Clojure.
The program is considered as a network of probabilistic (and deterministic)
choice points as specified by the user. Metropolis Hastings sampling is then
used to obtain samples from the probability distribution corresponding to
the probabilistic program. 
The system allows to condition and memoize probabilistic choice points and
can be extended by user defined distributions."}
  probabilistic-clojure.embedded.api
  (:use [clojure.set :only (union difference intersection)])
  (:use [probabilistic-clojure.utils.sampling :only (sample-from normalize random-selection random-selection-alias)]
	[probabilistic-clojure.utils.stuff :only (ensure-list error)]))

(in-ns 'probabilistic-clojure.embedded.api)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Basic data structures for the global store and choice points
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord State
  [choice-points recomputed newly-created possibly-removed failed?])

(defn fresh-state
  "Returns a fresh global store containing the given choice points.
The sets of recomputed, newly-created and possibly-removed choice points
are all initially empty and failed? is false."
  [choice-points]
  (State. choice-points #{} #{} #{} false))

(def ^:dynamic *global-store*
     (atom (fresh-state {})))

(defmacro with-fresh-store
  "Creates a fresh binding for the global store and evaluates the body in this context." 
  [choice-points & body]
  `(binding [*global-store* (atom (fresh-state ~choice-points))]
     ~@body))

(defn reset-store! []
  (swap! *global-store* (constantly (fresh-state {}))))

(defmacro update-in-store!
  "Syntax like update-in, but updates the global store as a side effect.
The global store should not be accessed directly, but only through this and
the related macros assoc-in-store! and fetch-store. This way the representation
of the global store could be changed with minimum effort."
  [[& keys] update-fn & args]
  `(swap! ~'*global-store*
	  update-in ~(vec keys) ~update-fn ~@args))

(defmacro assoc-in-store!
  "Assoc-in for the global store of choice points. See also update-in-store!."
  [[& keys] new-val]
  `(swap! ~'*global-store*
	  assoc-in ~(vec keys) ~new-val))

(defmacro fetch-store
  "Macro for reading from the global store. The syntax resembles the chaining macro ->, i.e.
each key-form gets an automatic first argument inserted."
  [& key-forms]
  `(-> (deref ~'*global-store*) ~@key-forms))

;;; choice points are maps with the following keys:
;;; name type recomputed recreate body dependents depends-on
;;;
;;; probabilistic choice points have additional keys:
;;; value log-lik sampler calc-log-lik proposer conditioned?

(def no-value ::unbound)

(defn make-choice-point
  "Create a new choice point with an unbound value and no dependencies."
  [name type whole body]
  {:name name :type type :recomputed no-value
   :whole whole :body body
   :dependents #{} :depends-on #{}})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Stuff to name choice points
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def ^:dynamic *call-stack* (list))

(defn current-caller
  "Returns the name of the choice point which is currently active or nil if no caller is active."
  []
  (when (seq *call-stack*)
    (first *call-stack*)))

;;; TODO: change this s.t. addr can be generated automatically [(with-tag <tag> ...) for local name change]

(def ^:dynamic *addr* (list))

(defn make-addr [tag]
  (cons tag *addr*))

(defmacro within [name & body]
  `(binding [*addr* ~name
	     *call-stack* (cons ~name *call-stack*)]
     ~@body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Tracking dependencies between choice points
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn update-dependencies
  "Registers a new dependency between the choice point with the given name and the current caller."
  [cp-name]
  (let [caller-name (current-caller)]
    (when caller-name
      (update-in-store! [:choice-points caller-name :depends-on]
			conj cp-name)
      (update-in-store! [:choice-points cp-name :dependents]
			conj caller-name))))

(defn retract-dependent
  "Register that the choice point cp-name no longer depends on dependent-name.
If cp-name has no dependents left afterwards it is tagged for possible removal."
  [cp-name dependent-name]
  (assert (contains? (fetch-store :choice-points (get cp-name) :dependents) dependent-name))
  (update-in-store! [:choice-points cp-name :dependents]
		    disj dependent-name)
  (when (empty? (fetch-store :choice-points (get cp-name) :dependents))
    (update-in-store! [:possibly-removed]
		      conj cp-name)))

(defn recompute-value
  "Recompute the value of the given choice point. Updates the dependencies for the new
value and registers the choice point as recomputed."
  [cp]
  (let [name (:name cp)]
    (update-in-store! [:recomputed] conj name)
    (within name
      (let [depended-on (fetch-store :choice-points (get name) :depends-on)]
	(assoc-in-store! [:choice-points name :depends-on] #{})
	(let [val ((:body cp))]
	  (doseq [used (difference depended-on
				   (fetch-store :choice-points (get name) :depends-on))]
	    (retract-dependent used name))
	  (assoc-in-store! [:choice-points name :recomputed] val)
	  val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Deterministic choice points
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn make-det-cp
  "Create a new determinstic choice point."
  [name whole body]
  (make-choice-point name ::deterministic whole body))

(defn det-cp-fn
  "This function gets called if a determinstic choice point is evaluated.
When the choice point is not already in the global store it is initialized,
its value is computed and the new choice point is returned.
Otherwise it is simply fetched from the store.
This function should not be called directly, but only in the context of det-cp."
  [name whole-fn body-fn]
  (if (contains? (fetch-store :choice-points) name)
    ((fetch-store :choice-points) name)
    (let [det-cp (make-det-cp name whole-fn body-fn)]
      (update-in-store! [:newly-created]
			conj name)
      (assoc-in-store! [:choice-points name]
		       det-cp)
      (recompute-value det-cp)
      (fetch-store :choice-points (get name)))))
  
(defmacro det-cp
  "Establishes a deterministic choice point with the given name tag for the code in the body."
  [tag & body]
  `(let [addr# *addr*
	 name# (make-addr ~tag)
	 body-fn# (fn [] ~@body)
	 whole-fn# (atom nil)]
     (swap! whole-fn#
	    (constantly
	      (fn []
		(det-cp-fn name# @whole-fn# body-fn#))))
     (det-cp-fn name# @whole-fn# body-fn#)))

(defmulti gv
  "Accesses the value of a choice point. When used in the body of another choice
point this creates a dependency between those choice points."
  :type)

(defmethod gv ::deterministic
  ;; Accesses the value of a deterministic choice point.
  ;; Takes care of dependencies and creates the choice point if necessary.
  [det-cp]
  (let [name (:name det-cp)]
    (if (contains? (fetch-store :choice-points) name)
      (let [val (fetch-store :choice-points (get name) :recomputed)]
	(update-dependencies name)
	val)
      ;; the choice point is not in the trace, thus we have to recreate it first
      (gv ((:whole det-cp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Probabilistic choice points
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn sample
  "Sample a new value for prob-cp."
  [prob-cp]
  (apply (:sampler prob-cp) (:recomputed prob-cp)))

(defn calc-log-lik
  "Calculate the probability of x given the current parameters of prob-cp."
  [prob-cp x]
  (apply (:calc-log-lik prob-cp) x (:recomputed prob-cp)))

(defn propose
  "Propose a new value new-x for prob-cp given that the current value is old-x.
Returns three values [new-x q(new-x | old-x) q(old-x | new-x)] where q(.|.) denotes the
proposal distribution."
  [prob-cp old-x]
  (apply (:proposer prob-cp) old-x (:recomputed prob-cp)))

(defn make-prob-cp
  "Creates a new probabilistic choice point."
  [name whole body sampler calc-log-lik proposer]
  (merge (make-choice-point name ::probabilistic whole body)
	 {:value no-value :log-lik 0 :sampler sampler :calc-log-lik calc-log-lik
	  :proposer proposer :conditioned? false}))

(defn update-log-lik
  "Update the probability for the given probabilistic choice point."
  [prob-cp-name]
  (let [prob-cp (fetch-store :choice-points (get prob-cp-name))]
    (assoc-in-store!
	   [:choice-points prob-cp-name :log-lik]
	   (calc-log-lik prob-cp (:value prob-cp)))))

(defn prob-cp-fn
  "As det-cp-fn, but for probabilistic choice points."
  [name whole-fn body-fn dist]
  (if (contains? (fetch-store :choice-points) name)
    ((fetch-store :choice-points) name)
    (let [prob-cp (make-prob-cp name whole-fn body-fn
				(:sampler dist)
				(:calc-log-lik dist)
				(:proposer dist))]
      (update-in-store! [:newly-created]
			conj name)
      (assoc-in-store! [:choice-points name]
		       prob-cp)
      (recompute-value prob-cp)
      (let [params (fetch-store :choice-points (get name) :recomputed)]
	(assoc-in-store! [:choice-points name :value]
			 (sample (fetch-store :choice-points (get name))))
	(update-log-lik name)
	(fetch-store :choice-points (get name))))))

(defn create-dist-map
  "Helper functions for def-prob-cp."
  [params dist-spec]
  (when-not (vector? params)
    (error "Provided parameters " params " are not a vector."))
  (let [keys #{:sampler :calc-log-lik :proposer}
	find-spec-for (fn [key]
			(let [spec-form (rest (drop-while #(not (= % key)) dist-spec))]
			  (when (empty? spec-form)
			    (error "You must provide an implementation for " key))
			  (take-while (complement keys) spec-form)))]
    (-> {}
	(assoc :sampler
	  (let [[args & body] (find-spec-for :sampler)]
	    (when-not (vector? args)
	      (error args " is not a parameter vector as required by ::sampler option"))
	    `(fn ~(vec (concat args params)) ~@body)))
	(assoc :calc-log-lik
	  (let [[args & body] (find-spec-for :calc-log-lik)]
	    (when-not (vector? args)
	      (error args " is not a parameter vector as required by ::calc-log-lik option"))
	    `(fn ~(vec (concat args params)) ~@body)))
	(assoc :proposer
	  (let [[args & body] (find-spec-for :proposer)]
	    (when-not (vector? args)
	      (error args " is not a parameter vector as required by ::proposer option"))
	    `(fn ~(vec (concat args params)) ~@body))))))
	    
(defmacro def-prob-cp
  "Macro to define probabilistic choice points.
Each choice point has a name and parameters. Furthermore, it must specify
functions :sampler, :calc-log-lik and :proposer. See the source of flip-cp
for an example."
  [name [& params] & dist-spec]
  (let [dist-map (create-dist-map (vec params) dist-spec)
	tag (gensym "tag")]
    `(defmacro ~name [~tag ~@params]
      `(let [~'addr# *addr*
	     ~'tag-name# (make-addr ~~tag)
	     ~'body-fn# (fn [] (list ~~@params))
	     ~'whole-fn# (atom nil)]
	 (swap! ~'whole-fn#
		(constantly
		 (fn []
		   (prob-cp-fn ~'tag-name# @~'whole-fn# ~'body-fn# ~'~dist-map))))
	 (prob-cp-fn ~'tag-name# @~'whole-fn# ~'body-fn# ~'~dist-map)))))

(defmethod gv ::probabilistic
  ;; Accesses the value of a probabilistic choice point
  [prob-cp]
  (let [name (:name prob-cp)]
    (if (contains? (fetch-store :choice-points) name)
      (let [val (fetch-store :choice-points (get name) :value)]
	(update-dependencies name)
	val)
      ;; the choice point is not in the trace, thus we have to recreate it first
      (gv ((:whole prob-cp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Metropolis Hastings sampling
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Traces failures

(defn trace-failure
  "Tags the current trace as failed. Used to implement rejection sampling."
  []
  (assoc-in-store! [:failed?] true))

(defn trace-failed? []
  (fetch-store :failed?))

;;; Sampling routines

(defn find-valid-trace
  "Returns a valid trace for the probabilistic program given as a no-arg function prob-chunk."
  [prob-chunk]
  (let [result (with-fresh-store {}
		 (let [cp (prob-chunk)]
		   (when-not (trace-failed?)
		     [cp (fetch-store :choice-points)])))]
    (if result
      result
      (recur prob-chunk))))

(defn cp-value
  "Returns the value of the choice point cp within the trace choice points."
  [cp choice-points]
  (if (= (:type cp) ::deterministic)
    (:recomputed (get choice-points (:name cp)))
    (:value (get choice-points (:name cp)))))

(defn monte-carlo-sampling
  "Simple Monte-Carlo sampling scheme which runs the whole probabilistic program
over and over again. Returns a lazy sequence of the obtained outcomes.
Rejections are not included in the output, so it may take a long time if the
rejection rate is high."
  [prob-chunk]
  (repeatedly (fn [] (let [[cp choice-points] (find-valid-trace prob-chunk)]
		       (cp-value cp choice-points)))))

;;; utility functions for sampling

(defn total-log-lik
  "Returns the total sum of the log. probabilities of all requested choice points
in the given trace.
Choice points not in the trace are allowed and contribute zero log. probability."
  [cp-names choice-points]
  (reduce + 0 (map (fn [cp-name]
		     (let [cp (choice-points cp-name)]
		       (case (:type cp)
			 ::probabilistic (:log-lik cp)
			 ::deterministic 0
			 0)))
		   cp-names)))

(defn remove-uncalled-choices
  "Remove all choice points from the global store which have not been called.
Starts from the choice points registered for possible removal and recursively
retracts further dependents.
Returns a set of the names of the removed choice points."
  []
  (loop [candidate-names (seq (fetch-store :possibly-removed))
	 result []]
    (if (empty? candidate-names)
      (set result)
      (let [candidate (fetch-store :choice-points (get (first candidate-names)))]
	(if (empty? (:dependents candidate))
	  (let [candidate-name (:name candidate)]
	    (update-in-store! [:choice-points]
			      dissoc candidate-name)
	    (doseq [cp-name (:depends-on candidate)]
	      (retract-dependent cp-name candidate-name))
	    (recur (concat (rest candidate-names)
			   (:depends-on candidate))
		   (conj result candidate-name)))
	  (recur (rest candidate-names) result))))))

;; Version using depth-first traversal to obtain topological ordering
;; of all choice points which have to updated if cp-name is changed
(defn ordered-dependencies
  "Return all direct and indirect dependents of cp-name in an order suitable for updating, i.e.
each choice point occurs before any of its dependents in this sequence (topologically sorted)."
  [cp-name choice-points]
  (let [visited (atom #{})
	ordered-deps (atom [])
	dfs-path (atom #{})
	back-edge? (fn [cp-name] (@dfs-path cp-name))]
    (letfn [(dfs-traverse [current-cp-name propagate?]
	      (swap! visited  conj current-cp-name)
	      (swap! dfs-path conj current-cp-name)
	      (let [current-cp (choice-points current-cp-name)
		    direct-deps (if (or propagate? (= (:type current-cp) ::deterministic))
				  (:dependents current-cp)
				  #{})]
		(doseq [dep-cp-name direct-deps]
		  (when (back-edge? dep-cp-name)
		    (error "Cyclic dependencies between " current-cp-name
			   " and " dep-cp-name " detected!"))
		  (when-not (@visited dep-cp-name)
		    (dfs-traverse dep-cp-name false)))
		(swap! dfs-path disj current-cp-name)
		(swap! ordered-deps (fn [deps] (cons current-cp-name deps)))))]
      (dfs-traverse cp-name true)
      @ordered-deps)))

(defn prob-choice-dist
  "Return a probability distribution for randomly choosing a choice point from the given trace.
Implements the heuristic to prefer choice points with many dependents."
  [choice-points]
  (letfn [(prob-choice? [cp]
	    (and (= (:type cp) ::probabilistic)
		 (not (:conditioned? cp))))]
    (normalize
     (into {}
	   (for [[name cp] choice-points
		 :when (prob-choice? cp)]
	     [name
	      (Math/sqrt (count (ordered-dependencies name choice-points)))])))))

(defn propagate-change-to
  "Propagate a change by recomputing all the given choice points in order."
  [cp-names]
  (doseq [dep-cp-name cp-names]
    (let [dep-cp (fetch-store :choice-points (get dep-cp-name))]
      (recompute-value dep-cp)
      (when (= (:type dep-cp) ::probabilistic)
	(update-log-lik (:name dep-cp))))))

;;; Conditioning and memoization

(defn cond-data [prob-cp cond-val]
  (let [name (:name prob-cp)
	val  (gv prob-cp)]
    (if (fetch-store :choice-points (get name) :conditioned?)
      (do (when-not (= cond-val val)
	    (error name " is already conditioned on value " val
		   " and cannot be changed to " cond-val))
	  cond-val)
      (do
	(assoc-in-store! [:choice-points name :value]
			 cond-val)
	(assoc-in-store! [:choice-points name :conditioned?]
			 true)
	(propagate-change-to (ordered-dependencies name (fetch-store :choice-points)))
	cond-val))))

(defmacro memo [tag cp-form & memo-args]
  `(det-cp ~tag
     (binding [*addr* (list ~@(rest cp-form) ~@memo-args)]
       (gv ~cp-form))))

;;; Finally the Metropolis Hastings sampling
;;; This combines the previous attempts for changing and fixed topologies.
;;; In case the topology remains unchanged the more efficient method is used.

;; Does not work so easily since for log. lik. computations we still need to track which
;; choice points are active and which are not!!!
;; (def ^:dynamic *remove-uncalled*
;;      "Should uncalled choices be removed?"
;;      true)
     
(defn metropolis-hastings-step [choice-points selected selection-dist]
  (with-fresh-store choice-points
    (let [selected-cp (choice-points selected)
	  change-set (ordered-dependencies (:name selected-cp) choice-points)
	  
	  [prop-val fwd-log-lik bwd-log-lik]
	  (propose selected-cp (:value selected-cp))]
      ;; Propose a new value for the selected choice point and propagate change to dependents
      (assoc-in-store! [:choice-points (:name selected-cp) :value]
		       prop-val)
      (propagate-change-to change-set)
      
      (if (trace-failed?)
	[choice-points ::rejected true selection-dist]
	(let [removed-cps (remove-uncalled-choices)
	      same-topology (and (empty? (fetch-store :newly-created))
				 (empty? removed-cps))
	      ;; Here we have the following invariants:
	      ;; * (assert (= (fetch-store :recomputed) (union (set change-set) (fetch-store :newly-created))))
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
				    (prob-choice-dist (fetch-store :choice-points)))]
	  ;; Randomly accept the new proposal according to the Metropolis Hastings formula
	  (if (< (Math/log (rand))
		 (+ (- prop-trace-log-lik trace-log-lik)
		    (- (Math/log (prop-selection-dist (:name selected-cp)))
		       (Math/log (selection-dist (:name selected-cp))))
		    (- bwd-trace-log-lik fwd-trace-log-lik)
		    (- bwd-log-lik fwd-log-lik)))
	    [(fetch-store :choice-points) ::accepted same-topology prop-selection-dist]
	    [choice-points ::rejected true selection-dist]))))))

(def ^:dynamic *info-steps*
     "Display some status information every *info-steps* many samples"
     500)

(def ^:dynamic *selection-dist-steps*
     "Force a refresh of the selection distribution after that many steps.
Anytime the topology has changed it is recomputed anyways."
     25000)

(defn new-update-sequence [dist]
  (random-selection-alias *selection-dist-steps* dist))

(defn metropolis-hastings-sampling [prob-chunk]
  (println "Trying to find a valid trace ...")
  (let [[cp choice-points] (find-valid-trace prob-chunk)]
    (println "Started sampling")
    (letfn [(samples [choice-points idx num-accepted num-top-changed update-seq selection-dist]
	      (lazy-seq
	       (let [update-seq (or (seq update-seq)
				    (new-update-sequence choice-points))
		     val (cp-value cp choice-points)
		     
		     [next-choice-points status same-topology next-selection-dist]
		     (metropolis-hastings-step choice-points (first update-seq) selection-dist)

		     output-info (= (mod idx *info-steps*) 0)]
		 (when output-info
		   (println idx ": " val)
		   (println "Log. lik.: " (total-log-lik (keys choice-points) choice-points))
		   (println "Accepted " num-accepted " out of last " *info-steps* " samples.")
		   (println "Topology changed on " num-top-changed " samples."))
		 (cons val
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
	(samples choice-points 0 0 0 (new-update-sequence selection-dist) selection-dist)))))
