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
  (:use [clojure.set :only (union difference)])
  (:use [probabilistic-clojure.utils.sampling :only (sample-from normalize)]
	[probabilistic-clojure.utils.stuff :only (ensure-list error)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Basic data structures for the global store and choice points
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrecord State
  [choice-points recomputed newly-created possibly-removed failed?])

(defn fresh-state [choice-points]
  (State. choice-points #{} #{} #{} false))

(def ^:dynamic *global-store*
     (atom (fresh-state {})))

(defmacro with-fresh-store [choice-points & body]
  `(binding [*global-store* (atom (fresh-state ~choice-points))]
     ~@body))

(defn reset-store! []
  (swap! *global-store* (constantly (fresh-state {}))))

(defmacro update-in-store! [[& keys] update-fn & args]
  `(swap! ~'*global-store*
	  update-in ~(vec keys) ~update-fn ~@args))

(defmacro assoc-in-store! [[& keys] new-val]
  `(swap! ~'*global-store*
	  assoc-in ~(vec keys) ~new-val))

(defmacro fetch-store [& keys]
  `(-> (deref ~'*global-store*) ~@keys))

;;; choice points are maps with the following keys:
;;; name type recomputed recreate body dependents depends-on
;;;
;;; probabilistic choice points have additional keys:
;;; value log-lik sampler calc-log-lik proposer conditioned?

(def no-value ::unbound)

(defn make-choice-point [name type whole body]
  {:name name :type type :recomputed no-value
   :whole whole :body body
   :dependents #{} :depends-on #{}})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Stuff to name choice points
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def ^:dynamic *call-stack* (list))

(defn current-caller []
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

(defn update-dependencies [cp-name]
  (let [caller-name (current-caller)]
    (when caller-name
      (update-in-store! [:choice-points caller-name :depends-on]
			conj cp-name)
      (update-in-store! [:choice-points cp-name :dependents]
			conj caller-name))))

(defn retract-dependent [cp-name dependent-name]
  (assert (contains? (fetch-store :choice-points (get cp-name) :dependents) dependent-name))
  (update-in-store! [:choice-points cp-name :dependents]
		    disj dependent-name)
  (when (empty? (fetch-store :choice-points (get cp-name) :dependents))
    (update-in-store! [:possibly-removed]
		      conj cp-name)))

(defn recompute-value [cp]
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

(defn make-det-cp [name whole body]
  (make-choice-point name ::deterministic whole body))

(defn det-cp-fn [name whole-fn body-fn]
  (if (contains? (fetch-store :choice-points) name)
    ((fetch-store :choice-points) name)
    (let [det-cp (make-det-cp name whole-fn body-fn)]
      (update-in-store! [:newly-created]
			conj name)
      (assoc-in-store! [:choice-points name]
		       det-cp)
      (recompute-value det-cp)
      (fetch-store :choice-points (get name)))))
  
(defmacro det-cp [tag & body]
  `(let [addr# *addr*
	 name# (make-addr ~tag)
	 body-fn# (fn [] ~@body)
	 whole-fn# (atom nil)]
     (swap! whole-fn#
	    (constantly
	      (fn []
		(det-cp-fn name# @whole-fn# body-fn#))))
     (det-cp-fn name# @whole-fn# body-fn#)))

(defmulti gv :type)

(defmethod gv ::deterministic
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

(defn sample [prob-cp]
  (apply (:sampler prob-cp) (:recomputed prob-cp)))

(defn calc-log-lik [prob-cp x]
  (apply (:calc-log-lik prob-cp) x (:recomputed prob-cp)))

(defn propose [prob-cp old-x]
  (apply (:proposer prob-cp) old-x (:recomputed prob-cp)))

(defn make-prob-cp [name whole body sampler calc-log-lik proposer]
  (merge (make-choice-point name ::probabilistic whole body)
	 {:value no-value :log-lik 0 :sampler sampler :calc-log-lik calc-log-lik
	  :proposer proposer :conditioned? false}))

(defn update-log-lik [prob-cp-name]
  (let [prob-cp (fetch-store :choice-points (get prob-cp-name))]
    (assoc-in-store!
	   [:choice-points prob-cp-name :log-lik]
	   (calc-log-lik prob-cp (:value prob-cp)))))

(defn prob-cp-fn [name whole-fn body-fn dist]
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

(defn create-dist-map [params dist-spec]
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

(defn trace-failure []
  (assoc-in-store! [:failed?] true))

(defn trace-failed? []
  (fetch-store :failed?))

;;; Sampling routines

(defn find-valid-trace [prob-chunk]
  (let [result (with-fresh-store {}
		 (let [cp (prob-chunk)]
		   (when-not (trace-failed?)
		     [cp (fetch-store :choice-points)])))]
    (if result
      result
      (recur prob-chunk))))

(defn cp-value [cp choice-points]
  (if (= (:type cp) ::deterministic)
    (:recomputed (get choice-points (:name cp)))
    (:value (get choice-points (:name cp)))))

(defn monte-carlo-sampling
  "Simple Monte-Carlo sampling scheme which simply runs the probabilistic program
num-samples many times. Returns a lazy sequence of the obtained outcomes."
  [num-samples prob-chunk]
  (repeatedly num-samples
	      (fn [] (let [[cp choice-points] (find-valid-trace prob-chunk)]
				(cp-value cp choice-points)))))

;;; utility functions for sampling

(defn total-log-lik [cp-names choice-points]
  (reduce + (map (fn [cp-name]
		   (let [cp (choice-points cp-name)]
		     (if (= (:type cp) ::probabilistic)
		       (:log-lik cp)
		       0)))
		 cp-names)))

(defn remove-uncalled-choices []
  (loop [candidate-names (fetch-store :possibly-removed)
	 result []]
    (if (empty? candidate-names)
      result
      (let [candidate (fetch-store :choice-points (get (first candidate-names)))]
	(if (empty? (:dependents candidate))
	  (do (update-in-store! [:choice-points]
				dissoc (:name candidate))
	      (doseq [cp-name (:depends-on candidate)]
		(retract-dependent cp-name (:name candidate)))
	      (recur (concat (rest candidate-names)
			     (:depends-on candidate))
		     (conj result candidate)))
	  (recur (rest candidate-names) result))))))

;; Version using depth-first traversal to obtain topological ordering
;; of all choice points which have to updated if cp-name is changed
(defn ordered-dependencies [cp-name choice-points]
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

(defn prob-choice-dist [choice-points]
  (letfn [(prob-choice? [cp]
	    (and (= (:type cp) ::probabilistic)
		 (not (:conditioned? cp))))]
    (normalize
     (into {}
	   (for [[name cp] choice-points
		 :when (prob-choice? cp)]
	     [name
	      (Math/sqrt (count (ordered-dependencies name choice-points)))])))))

(defn propagate-change-to [cp-names]
  (doseq [dep-cp-name cp-names]
    (let [dep-cp (fetch-store :choice-points (get dep-cp-name))]
      (recompute-value dep-cp)
      (when (= (:type dep-cp) ::probabilistic)
	(update-log-lik (:name dep-cp))))))

;;; The actual Metropolis Hastings sampling

(defn sampling-step [choice-points]
  (with-fresh-store choice-points
    (let [prob-choices (prob-choice-dist choice-points)
	  selected-cp (choice-points (sample-from prob-choices))
	  change-set (ordered-dependencies (:name selected-cp) choice-points)
	  trace-log-lik (total-log-lik change-set choice-points)
	  
	  [prop-val fwd-log-lik bwd-log-lik]
	  (propose selected-cp (:value selected-cp))]
      (assoc-in-store! [:choice-points (:name selected-cp) :value]
		       prop-val)
      (propagate-change-to change-set)
      (if (trace-failed?)
	choice-points
	(let [all-new-choice-points (fetch-store :choice-points)
	      fwd-trace-log-lik (total-log-lik (fetch-store :newly-created) all-new-choice-points)
	      removed-cps (remove-uncalled-choices)
	      bwd-trace-log-lik (total-log-lik (map :name removed-cps) all-new-choice-points)
	      prop-trace-log-lik (total-log-lik (difference
						 ;; TODO: What about reweighting of reused choice-points???
						 ;; (union (set change-set) (-> @*global-store* :newly-created))
						 (fetch-store :recomputed)
						 (set (map :name removed-cps)))
						all-new-choice-points)
	      prop-prob-choices (prob-choice-dist (fetch-store :choice-points))]
	  (if (< (Math/log (rand))
		 (+ (- prop-trace-log-lik trace-log-lik)
		    (- (Math/log (prop-prob-choices (:name selected-cp)))
		       (Math/log (prob-choices (:name selected-cp))))
		    (- bwd-trace-log-lik fwd-trace-log-lik)
		    (- bwd-log-lik fwd-log-lik)))
	    (fetch-store :choice-points)
	    choice-points))))))

(defn sample-traces [prob-chunk]
  (println "Trying to find a valid trace ...")
  (let [[cp choice-points] (find-valid-trace prob-chunk)]
    (println "Started sampling")
    (letfn [(samples [choice-points idx accepted]
	      (lazy-seq
	       (let [val (cp-value cp choice-points)
		     next-choices (sampling-step choice-points)
		     output? (= (mod idx 500) 0)
		     accepted (if (= choice-points next-choices)
				accepted
				(inc accepted))]
		 (when output?
		   (println idx ": " val)
		   (println "Log. lik.: " (total-log-lik (keys choice-points) choice-points))
		   (println "Accepted " accepted " out of last 500 samples"))
		 (cons val
		       (samples next-choices (inc idx)
				(if output? 0 accepted))))))]
      (samples choice-points 0 0))))

;;; faster sampling for fixed topology ==> TODO: combine for general sampling routine!!!

(defn sampling-step-fixed [choice-points selected all-dependencies]
  (with-fresh-store choice-points
    (let [selected-cp (choice-points selected)
	  change-set  (ordered-dependencies (:name selected-cp) choice-points)
	  trace-log-lik (total-log-lik change-set choice-points)
	  
	  [prop-val fwd-log-lik bwd-log-lik]
	  (propose selected-cp (:value selected-cp))]
      (assoc-in-store! [:choice-points (:name selected-cp) :value]
		       prop-val)
      (propagate-change-to change-set)

      (if (trace-failed?)
	[choice-points false]
	(do (let [removed-cps (remove-uncalled-choices)]
	      (when-not (empty? (fetch-store :newly-created))
		(error "New choice points created during fixed sampling: "
		       (pr-str (map :name (fetch-store :newly-created)))))
	      (when-not (empty? removed-cps)
		(error "Choice points deleted during fixed sampling: "
		       (pr-str (map :name removed-cps)))))
	    (let [prop-trace-log-lik (total-log-lik (fetch-store :recomputed)
						    (fetch-store :choice-points))]
	      (if (< (Math/log (rand))
		     (+ (- prop-trace-log-lik trace-log-lik)
			(- bwd-log-lik fwd-log-lik)))
		[(fetch-store :choice-points) true]
		[choice-points false])))))))

(defn sample-traces-fixed [prob-chunk select-update]
  (println "Trying to find a valid trace ...")
  (let [[cp choice-points] (find-valid-trace prob-chunk)]
    (println "Generating update sequence ...")
    (let [update-seq  (select-update (prob-choice-dist choice-points))]
      (println "Started sampling")
      (letfn [(samples [choice-points idx accepted update-seq all-dependencies]
		(if (seq update-seq)
		  (lazy-seq
		   (let [val (cp-value cp choice-points)
			 [next-choices accepted?]
			 (sampling-step-fixed choice-points
					      (first update-seq)
					      all-dependencies)
			 output? (= (mod idx 500) 0)
			 accepted (if accepted? (inc accepted) accepted)]
		     (when output?
		       (println idx ": " val)
		       (println "Log. lik.: " (total-log-lik (keys choice-points) choice-points))
		       (println "Accepted " accepted " out of last 500 samples"))
		     (cons val
			   (samples next-choices (inc idx)
				    (if output? 0 accepted)
				    (rest update-seq)
				    all-dependencies))))
		  ()))]
	(samples choice-points 0 0 update-seq
		 (do (println "Caching dependencies ...")
		     (time
		      (into {} (for [cp-name (keys choice-points)]
				 [cp-name (ordered-dependencies cp-name choice-points)])))))))))

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
