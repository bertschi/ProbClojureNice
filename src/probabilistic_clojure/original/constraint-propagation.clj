;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Probabilistic programming using constraint propagation
;;;; to efficiently track dependencies between choice points
;;;;
;;;; Should be simpler due to immutable datastructures
;;;; and using the insights obtained from failed attempts
;;;; in Common Lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ns constraint.prob
  (:use [clojure.set :only (union difference)])
  (:use [incanter.core :only (gamma view)]
	[incanter.stats :only (sample-normal pdf-normal sample-dirichlet sample-beta pdf-beta mean)]
	[incanter.charts :only (histogram xy-plot add-lines bar-chart line-chart add-categories)])
  (:import org.apache.commons.math.special.Gamma))
;;  (:import cern.jet.stat.tdouble.Gamma))

(defrecord State
  [choice-points recomputed newly-created possibly-removed failed?])

(defn fresh-state [choice-points]
  (State. choice-points #{} #{} #{} false))

(def *global-store*
     (atom (fresh-state {})))

(defmacro with-fresh-store [choice-points & body]
  `(binding [*global-store* (atom (fresh-state ~choice-points))]
     ~@body))

(defn reset-store []
  (swap! *global-store* (constantly (fresh-state {}))))

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

(defn make-det-cp [name whole body]
  (make-choice-point name ::deterministic whole body))

(defn sample [prob-cp]
  (apply (:sampler prob-cp) (:recomputed prob-cp)))

(defn calc-log-lik [prob-cp x]
  (apply (:calc-log-lik prob-cp) x (:recomputed prob-cp)))

(defn propose [prob-cp old-x]
  ((:proposer prob-cp) prob-cp old-x))

(defn make-prob-cp
  ([name whole body sampler calc-log-lik]
     (let [prob-cp (make-prob-cp name whole body sampler calc-log-lik nil)]
       (assoc prob-cp
	 :proposer
	 (fn [prob-cp old-x]
	   (let [new-x (sample prob-cp)
		 log-fwd-lik (calc-log-lik prob-cp new-x)
		 log-bwd-lik (calc-log-lik prob-cp old-x)]
	     [new-x log-fwd-lik log-bwd-lik])))))
  ([name whole body sampler calc-log-lik proposer]
     (merge (make-choice-point name ::probabilistic whole body)
	    {:value no-value :log-lik 0 :sampler sampler :calc-log-lik calc-log-lik
	     :proposer proposer :conditioned? false})))

(def flip-dist
     {:sampler (fn [p] (< (rand) p))
      :calc-log-lik (fn [x p] (Math/log (if x p (- 1 p))))
      :proposer (fn [cp old-x] [(not old-x) 0 0])})

(def *call-stack* (list))

(defn current-caller []
  (when (seq *call-stack*)
    (first *call-stack*)))

(def *addr* (list))

(defn make-addr [tag]
  (cons tag *addr*))

(defmacro within [name & body]
  `(binding [*addr* ~name
	     *call-stack* (cons ~name *call-stack*)]
     ~@body))

(defn retract-dependent [cp-name dependent-name]
  (assert (contains? (-> @*global-store* :choice-points (get cp-name) :dependents) dependent-name))
  (swap! *global-store*
	 update-in
	 [:choice-points cp-name :dependents]
	 disj dependent-name)
  (when (empty? (-> @*global-store* :choice-points (get cp-name) :dependents))
    (swap! *global-store*
	   update-in
	   [:possibly-removed]
	   conj cp-name)))

(defn recompute-value [cp]
  (let [name (:name cp)]
    (swap! *global-store* update-in [:recomputed] conj name)
    (within name
      (let [depended-on (-> @*global-store* :choice-points (get name) :depends-on)]
	(swap! *global-store*
	       assoc-in [:choice-points name :depends-on] #{})
	(let [val ((:body cp))]
	  (doseq [used (difference depended-on
				   (-> @*global-store* :choice-points (get name) :depends-on))]
	    (retract-dependent used name))
	  (swap! *global-store*
		 assoc-in [:choice-points name :recomputed] val)
	  val)))))

(defn det-cp-fn [name whole-fn body-fn]
  (if (contains? (:choice-points @*global-store*) name)
    ((:choice-points @*global-store*) name)
    (let [det-cp (make-det-cp name whole-fn body-fn)]
      (swap! *global-store*
	     update-in
	     [:newly-created]
	     conj name)
      (swap! *global-store*
	     assoc-in
	     [:choice-points name]
	     det-cp)
      (recompute-value det-cp)
      (-> @*global-store* :choice-points (get name)))))
  
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

(defn update-dependencies [cp-name]
  (let [caller-name (current-caller)]
    (when caller-name
      (swap! *global-store*
	     update-in [:choice-points caller-name :depends-on]
	     conj cp-name)
      (swap! *global-store*
	     update-in [:choice-points cp-name :dependents]
	     conj caller-name))))

(defmulti gv :type)

(defmethod gv ::deterministic
  [det-cp]
  (let [name (:name det-cp)]
    (if (contains? (-> @*global-store* :choice-points) name)
      (let [val (-> @*global-store* :choice-points (get name) :recomputed)]
	(update-dependencies name)
	val)
      ;; the choice point is not in the trace, thus we have to recreate it first
      (gv ((:whole det-cp))))))

(defn test-dynamic-dependencies []
  (reset-store)
  (let [a (det-cp :a true)
	b (det-cp :b (list :hello (gv a)))
	c (det-cp :c
	   (do (println "Here")
	       (if (gv a) (list (gv b) :c) :nope)))
	show-cps (fn []
		   (println "Recomputed: " (:recomputed @*global-store*))
		   (println "Newly created: " (:newly-created @*global-store*))
		   (println "Possibly removed: " (:possibly-removed @*global-store*))
		   (doseq [[name cp] (:choice-points @*global-store*)]
		     (println name ": " (:recomputed cp)
			      " dependents " (:dependents cp)
			      " depends on " (:depends-on cp))))
	set-value! (fn [cp val]
		     (swap! *global-store*
			    assoc-in [:choice-points (:name cp) :recomputed] val))
	refresh (fn [] (swap! *global-store* (constantly
					      (fresh-state (:choice-points @*global-store*)))))]
		     
    (show-cps)
    (refresh)    
    (set-value! b :huhu)
    (recompute-value c)
    (show-cps)
    (refresh)
    (set-value! a false)
    (recompute-value c)
    (show-cps)
    (refresh)    
    (set-value! b :nowhere)
    (recompute-value c)
    (show-cps)
    (refresh)
    (swap! *global-store* update-in [:choice-points] dissoc (:name b))
    (set-value! a true)
    (recompute-value c)
    (show-cps)))

(defn update-log-lik [prob-cp-name]
  (let [prob-cp (-> @*global-store* :choice-points (get prob-cp-name))]
    (swap! *global-store*
	   assoc-in
	   [:choice-points prob-cp-name :log-lik]
	   (calc-log-lik prob-cp (:value prob-cp)))))

(defn flip-cp-fn [name whole-fn body-fn]
  (if (contains? (:choice-points @*global-store*) name)
    ((:choice-points @*global-store*) name)
    (let [flip-cp (make-prob-cp name whole-fn body-fn
				(:sampler flip-dist)
				(:calc-log-lik flip-dist)
				(:proposer flip-dist))]
      (swap! *global-store*
	     update-in
	     [:newly-created]
	     conj name)
      (swap! *global-store*
	     assoc-in
	     [:choice-points name]
	     flip-cp)
      (recompute-value flip-cp)
      (let [params (-> @*global-store* :choice-points (get name) :recomputed)]
	(swap! *global-store*
	       assoc-in
	       [:choice-points name :value]
	       (sample (-> @*global-store* :choice-points (get name))))
	(update-log-lik name)
	(-> @*global-store* :choice-points (get name))))))
  
(defmacro flip-cp [tag p]
  `(let [addr# *addr*
	 name# (make-addr ~tag)
	 body-fn# (fn [] (list ~p))
	 whole-fn# (atom nil)]
     (swap! whole-fn#
	    (constantly
	      (fn []
		(flip-cp-fn name# @whole-fn# body-fn#))))
     (flip-cp-fn name# @whole-fn# body-fn#)))

(defmethod gv ::probabilistic
  [prob-cp]
  (let [name (:name prob-cp)]
    (if (contains? (-> @*global-store* :choice-points) name)
      (let [val (-> @*global-store* :choice-points (get name) :value)]
	(update-dependencies name)
	val)
      ;; the choice point is not in the trace, thus we have to recreate it first
      (gv ((:whole prob-cp))))))

(defn get-all-dependents [cp-name]
  (letfn [(all-deps-loop [seens deps propagate?]
	    (let [unseens (difference deps seens)]
	      (if (empty? unseens)
		deps
		(let [next-cp-name (first unseens)
		      next-cp (-> @*global-store* :choice-points (get next-cp-name))
		      direct-deps (if (or propagate? (= (:type next-cp) ::deterministic))
				    (:dependents next-cp)
				    #{})]
		  (recur (conj seens next-cp-name)
			 (union direct-deps deps)
			 false)))))]
    (all-deps-loop #{} #{cp-name} true)))

(defn local-dependency-ordering [cp-name]
  (map (fn [dep] [cp-name dep])
       (-> @*global-store* :choice-points (get cp-name) :dependents)))

(defn topological-sort [elements constraints tie-breaker]
  (letfn [(topsort-loop [remaining-elements remaining-constraints result]
	    (let [minimal-elements
		  (remove (fn [ele]
			    (some (fn [[_ upper]] (= ele upper)) remaining-constraints))
			  remaining-elements)]
	      (if (empty? minimal-elements)
		(if (empty? remaining-elements)
		  (reverse result)
		  (throw (Error. "Inconsistent dependency graph")))
		(let [choice (if (= (count minimal-elements) 1)
			       (first minimal-elements)
			       (tie-breaker minimal-elements (reverse result)))]
		  (recur (remove #(= % choice) remaining-elements)
			 (remove (fn [c] (some #(= % choice) c)) remaining-constraints)
			 (cons choice result))))))]
    (topsort-loop elements constraints (list))))

;; (defn ordered-dependencies [cp-name]
;;   (let [cps-to-order (get-all-dependents cp-name)]
;;     (topological-sort cps-to-order
;; 		      (mapcat local-dependency-ordering cps-to-order)
;; 		      (fn [candidates _] (first candidates)))))

(defn error [& args]
  (throw (Error. (apply str args))))

;; Version using depth-first traversal to obtain topological ordering
;; of all choice points which have to updated if cp-name is changed
(defn ordered-dependencies [cp-name]
  (let [visited (atom #{})
	ordered-deps (atom [])
	dfs-path (atom #{})
	back-edge? (fn [cp-name] (@dfs-path cp-name))]
    (letfn [(dfs-traverse [current-cp-name propagate?]
	      (swap! visited  conj current-cp-name)
	      (swap! dfs-path conj current-cp-name)
	      (let [current-cp (-> @*global-store* :choice-points (get current-cp-name))
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

(defn test-topsort []
  (reset-store)
  (let [a (det-cp :a :a)
	b (det-cp :b (list :b (gv a)))
	c (det-cp :c (list :c (gv b) (gv a)))
	p (flip-cp :p (if (gv a) 0.2 0.8))
	d (det-cp :d (list :d (gv p) (gv c)))
	e (det-cp :e (list :e (gv p)))]
    (println (get-all-dependents (:name a)))
    (println (ordered-dependencies (:name a)))))

(defn trace-failure []
  (swap! *global-store*
	 assoc-in [:failed?] true))

(defn trace-failed? []
  (:failed? @*global-store*))

(defn find-valid-trace [prob-chunk]
  (with-fresh-store {}
    (let [cp (prob-chunk)]
      (if (trace-failed?)
	(recur prob-chunk)
	[cp (:choice-points @*global-store*)]))))

;;; The example that is supposed to work

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
       
(defn test-monte-carlo [num-samples prob-chunk]
  (frequencies (repeatedly num-samples
			   (fn [] (first (find-valid-trace prob-chunk))))))

(defn total-log-lik [cp-names]
  (reduce + (map (fn [cp-name]
		   (let [cp (-> @*global-store* :choice-points (get cp-name))]
		     (if (= (:type cp) ::probabilistic)
		       (:log-lik cp)
		       0)))
		 cp-names)))

(defn remove-uncalled-choices []
  (loop [candidate-names (-> @*global-store* :possibly-removed)
	 result []]
    (if (empty? candidate-names)
      result
      (let [candidate (-> @*global-store* :choice-points (get (first candidate-names)))]
	(if (empty? (:dependents candidate))
	  (do (swap! *global-store* update-in [:choice-points]
		     dissoc (:name candidate))
	      (doseq [cp-name (:depends-on candidate)]
		(retract-dependent cp-name (:name candidate)))
	      (recur (concat (rest candidate-names)
			     (:depends-on candidate))
		     (conj result candidate)))
	  (recur (rest candidate-names) result))))))

(declare normalize)

(defn prob-choice-dist [choice-points]
  (letfn [(prob-choice? [cp]
	    (and (= (:type cp) ::probabilistic)
		 (not (:conditioned? cp))))]
    (with-fresh-store choice-points
      (normalize
       (into {}
	     (for [[name cp] choice-points
		   :when (prob-choice? cp)]
	       [name
		(Math/sqrt (count (ordered-dependencies name)))]))))))
		;; (Math/sqrt (max 1 (count (:dependents cp))))]))))))

(declare sample-from)

(defn propagate-change-to [cp-names]
  (doseq [dep-cp-name cp-names]
    (let [dep-cp (-> @*global-store* :choice-points (get dep-cp-name))]
      (recompute-value dep-cp)
      (when (= (:type dep-cp) ::probabilistic)
	(update-log-lik (:name dep-cp))))))

(defn sampling-step [choice-points]
  (with-fresh-store choice-points
    (let [prob-choices (prob-choice-dist choice-points)
	  selected-cp (choice-points (sample-from prob-choices))
	  change-set (ordered-dependencies (:name selected-cp))
	  trace-log-lik (total-log-lik change-set)
	  
	  [prop-val fwd-log-lik bwd-log-lik]
	  (propose selected-cp (:value selected-cp))]
      ;; (println "Proposing " (:name selected-cp) " for " (count change-set) " changes " change-set)
      (swap! *global-store*
	     assoc-in [:choice-points (:name selected-cp) :value] prop-val)
      (propagate-change-to change-set)
      ;; (println (-> @*global-store* :newly-created) " new choice points and "
      ;; 	       (-> @*global-store* :possibly-removed) " tagged for removal")
      (if (trace-failed?)
	choice-points
	(let [;; prop-trace-log-lik
	      ;; ;; (total-log-lik (:recomputed @*global-store*))
	      ;; (total-log-lik change-set)
	      fwd-trace-log-lik (total-log-lik (-> @*global-store* :newly-created))
	      removed-cps (remove-uncalled-choices)
	      bwd-trace-log-lik (total-log-lik (map :name removed-cps))
	      prop-trace-log-lik (total-log-lik (difference ;; (union (set change-set) (-> @*global-store* :newly-created))
						 (-> @*global-store* :recomputed)
						 (set (map :name removed-cps))))
	      prop-prob-choices (prob-choice-dist (-> @*global-store* :choice-points))]
	  ;; (assert (= prop-trace-len (+ trace-len (count (:newly-created @*global-store*))
	  ;; 			       (- (count removed-cps)))))
	  ;; (println "Log. lik. changed from "
	  ;; 	   (with-fresh-store choice-points (total-log-lik (keys choice-points)))
	  ;; 	   " to " (total-log-lik (keys (:choice-points @*global-store*)))
	  ;; 	   " (" (- prop-trace-log-lik trace-log-lik) ")")
	  (if (< (Math/log (rand))
		 (+ (- prop-trace-log-lik trace-log-lik)
		    (- (Math/log (prop-prob-choices (:name selected-cp)))
		       (Math/log (prob-choices (:name selected-cp))))
		    (- bwd-trace-log-lik fwd-trace-log-lik)
		    (- bwd-log-lik fwd-log-lik)))
	    (:choice-points @*global-store*)
	    choice-points))))))

(defn sample-traces [prob-chunk]
  (println "Trying to find a valid trace ...")
  (let [[cp choice-points] (find-valid-trace prob-chunk)
	output-name (:name cp)]
    (println "Started sampling")
    (letfn [(samples [choice-points idx accepted]
	      (lazy-seq
	       (let [val (if (= (:type cp) ::deterministic)
			   (:recomputed (get choice-points output-name))
			   (:value (get choice-points output-name)))
		     next-choices (sampling-step choice-points)
		     output? (= (mod idx 500) 0)
		     accepted (if (= choice-points next-choices)
				accepted
				(inc accepted))]
		 (when output?
		   (println idx ": " val)
		   (println "Log. lik.: " (with-fresh-store choice-points
					    (total-log-lik (keys choice-points))))
		   (println "Accepted " accepted " out of last 500 samples"))
		 (cons val
		       (samples next-choices (inc idx)
				(if output? 0 accepted))))))]
      (samples choice-points 0 0))))
		      
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Some more choice points and Gaussian mixture models
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn prob-cp-fn [name whole-fn body-fn dist]
  (if (contains? (:choice-points @*global-store*) name)
    ((:choice-points @*global-store*) name)
    (let [prob-cp (if (contains? dist :proposer)
		    (make-prob-cp name whole-fn body-fn
				  (:sampler dist)
				  (:calc-log-lik dist)
				  (:proposer dist))
		    (make-prob-cp name whole-fn body-fn
				  (:sampler dist)
				  (:calc-log-lik dist)))]
      (swap! *global-store*
	     update-in
	     [:newly-created]
	     conj name)
      (swap! *global-store*
	     assoc-in
	     [:choice-points name]
	     prob-cp)
      (recompute-value prob-cp)
      (let [params (-> @*global-store* :choice-points (get name) :recomputed)]
	(swap! *global-store*
	       assoc-in
	       [:choice-points name :value]
	       (sample (-> @*global-store* :choice-points (get name))))
	(update-log-lik name)
	(-> @*global-store* :choice-points (get name))))))
  
;; (defn def-prob-cp-expansion [addr-name params dist-spec]
;;   `(let [addr# *addr*
;; 	 name# (make-addr ~addr-name)
;; 	 body-fn# (fn [] (list ~@params))
;; 	 whole-fn# (atom nil)]
;;      (swap! whole-fn#
;; 	    (constantly
;; 	     (fn []
;; 	       (prob-cp-fn name# @whole-fn# body-fn# ~dist-spec))))
;;      (prob-cp-fn name# @whole-fn# body-fn# ~dist-spec)))

;; (defmacro def-prob-cp [cp-name [& params] dist-spec]
;;   `(defmacro ~cp-name [~@params]
;;      ~(def-prob-cp-expansion ~(keyword cp-name) ~params ~dist-spec)))
     
;; (def-prob-cp flipper [p] flip-dist)
;;; somehow nested backquotes not working as desired yet

(def gaussian-dist
     {:sampler (fn [mu sdev] (sample-normal 1 :mean mu :sd sdev))
      :calc-log-lik (fn [x mu sdev] (Math/log (pdf-normal x :mean mu :sd sdev)))
      :proposer (fn [cp old-x]
		  (let [proposal-sd 0.7
			new-x (sample-normal 1 :mean old-x :sd proposal-sd)]
		    [new-x
		     (Math/log (pdf-normal new-x :mean old-x :sd proposal-sd))
		     (Math/log (pdf-normal old-x :mean new-x :sd proposal-sd))]))})

(defmacro gaussian-cp [tag mu sdev]
  `(let [addr# *addr*
	 name# (make-addr ~tag)
	 body-fn# (fn [] (list ~mu ~sdev))
	 whole-fn# (atom nil)]
     (swap! whole-fn#
	    (constantly
	     (fn []
	       (prob-cp-fn name# @whole-fn# body-fn# gaussian-dist))))
     (prob-cp-fn name# @whole-fn# body-fn# gaussian-dist)))

(defn pdf-dirichlet [ps alphas]
  (let [norm (/ (reduce * (map gamma alphas))
		(gamma (reduce + alphas)))]
    (/ (reduce * (map (fn [p a] (Math/pow p (- a 1))) ps alphas))
       norm)))

(defn log-pdf-dirichlet [ps alphas]
  (let [log-gamma (fn [x] (Gamma/logGamma x))
	norm (- (reduce + (map log-gamma alphas))
		(log-gamma (reduce + alphas)))]
    (- (reduce + (map (fn [p a] (* (- a 1) (Math/log p))) ps alphas))
       norm)))

(def dirichlet-dist
     (letfn [(proposal-alphas [alphas]
	       (for [a alphas] (* 88 a)))]
       {:sampler (fn [alphas] (first (sample-dirichlet 2 alphas)))
	:calc-log-lik (fn [ps alphas] (log-pdf-dirichlet ps alphas))
	:proposer (fn [cp old-ps]
		    (let [new-ps (first (sample-dirichlet 2 (proposal-alphas old-ps)))]
		      [new-ps
		       (log-pdf-dirichlet new-ps (proposal-alphas old-ps))
		       (log-pdf-dirichlet old-ps (proposal-alphas new-ps))]))}))

(defmacro dirichlet-cp [tag alphas]
  `(let [addr# *addr*
	 name# (make-addr ~tag)
	 body-fn# (fn [] (list ~alphas))
	 whole-fn# (atom nil)]
     (swap! whole-fn#
	    (constantly
	     (fn []
	       (prob-cp-fn name# @whole-fn# body-fn# dirichlet-dist))))
     (prob-cp-fn name# @whole-fn# body-fn# dirichlet-dist)))

(defn sample-from
  "Sample from a discrete distribution implemented as a hash-map from
values to probabilities."
  [dist]
  (when (seq dist)
    (let [total (reduce + (vals dist))
	  threshold (rand)]
      (loop [cum-p 0
	     [[v p] & more] (seq dist)]
	(if (< threshold (+ cum-p p))
	  v
	  (recur (+ cum-p p) more))))))

(defn normalize [dist]
  (let [total (reduce + (vals dist))]
    (into {} (for [[x p] dist] [x (/ p total)]))))

(def discrete-dist
     {:sampler (fn [dist] (sample-from dist))
      :calc-log-lik (fn [x dist]
		      (if (contains? dist x)
			(Math/log (dist x))
			(Math/log 0)))
      :proposer (fn [cp old-x]
      		  (let [[dist] (:recomputed cp)
			prop-dist (normalize (assoc dist old-x 0))
      			new-x (sample-from prop-dist)]
      		    [new-x
      		     ((:calc-log-lik cp) new-x prop-dist)
      		     ((:calc-log-lik cp) old-x (normalize (assoc dist new-x 0)))]))})

(defmacro discrete-cp [tag dist]
  `(let [addr# *addr*
	 name# (make-addr ~tag)
	 body-fn# (fn [] (list ~dist))
	 whole-fn# (atom nil)]
     (swap! whole-fn#
	    (constantly
	     (fn []
	       (prob-cp-fn name# @whole-fn# body-fn# discrete-dist))))
     (prob-cp-fn name# @whole-fn# body-fn# discrete-dist)))

;;; conditioning is done by setting the value of the choice-point and
;;; then calling it

(defn cond-data [prob-cp cond-val]
  (let [name (:name prob-cp)
	val  (gv prob-cp)]
    (if (-> @*global-store* :choice-points (get name) :conditioned?)
      (do (when-not (= cond-val val)
	    (error name " is already conditioned on value " val
		   " and cannot be changed to " cond-val))
	  cond-val)
      (do
	(swap! *global-store*
	       assoc-in [:choice-points name :value] cond-val)
	(swap! *global-store*
	       assoc-in [:choice-points name :conditioned?] true)
	(propagate-change-to (ordered-dependencies name))
	cond-val))))

;;; Mixture model as an example

(defn generate-data []
  (let [mu (fn [] (sample-from {-5 0.2, 0 0.7, 8 0.1}))]
    (lazy-seq (cons (sample-normal 1 :mean (mu))
		    (generate-data)))))

(def data (take 42 (generate-data)))

(defn mixture-1 [comp-labels data]
  (det-cp :mixture
    (let [comp-weights (dirichlet-cp :weights (for [_ comp-labels] 10.0))
	  comp-mus (zipmap comp-labels
			   (for [label comp-labels] (gaussian-cp [:mu label] 0.0 10.0)))]
      (loop [points data
	     mus {}
	     assignment []
	     idx 0]
	(if (empty? points)
	  [mus (gv comp-weights) assignment]
	  (let [comp (discrete-cp [:comp idx] (zipmap comp-labels (gv comp-weights)))
		mu-comp (det-cp [:mu-comp idx] (gv (get comp-mus (gv comp))))]
	    (cond-data (gaussian-cp [:mu idx] (gv mu-comp) 1.0) (first points))
	    (recur (rest points)
		   (assoc mus (gv comp) (gv mu-comp))
		   (conj assignment (gv comp))
		   (inc idx))))))))

(defn mixture-2 [comp-labels data]
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
;;; Finally, extend this to a Dirichlet process such that also the number of
;;; components is learned
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro memo [tag cp-form & memo-args]
  `(det-cp ~tag
     (binding [*addr* (list ~@(rest cp-form) ~@memo-args)]
       (gv ~cp-form))))

(def beta-dist
     {:sampler (fn [alpha beta] (sample-beta 1 :alpha alpha :beta beta))
      :calc-log-lik (fn [x alpha beta] (Math/log (pdf-beta x :alpha alpha :beta beta)))
      :proposer (fn [cp old-x]
		  (let [[alpha beta] (:recomputed cp)
			new-x (sample-beta 1 :alpha alpha :beta beta)]
		    [new-x
		     (Math/log (pdf-beta new-x :alpha alpha :beta beta))
		     (Math/log (pdf-beta old-x :alpha alpha :beta beta))]))})

(defmacro beta-cp [tag alpha beta]
  `(let [addr# *addr*
	 name# (make-addr ~tag)
	 body-fn# (fn [] (list ~alpha ~beta))
	 whole-fn# (atom nil)]
     (swap! whole-fn#
	    (constantly
	     (fn []
	       (prob-cp-fn name# @whole-fn# body-fn# beta-dist))))
     (prob-cp-fn name# @whole-fn# body-fn# beta-dist)))

(defn pick-a-stick [alpha idx]
  (let [stick (beta-cp [:pick :stick idx] 1 alpha)
	stop  (flip-cp [:pick :stop idx] (gv stick))]
    (det-cp [:pick idx]
      (if (gv stop)
	idx
	(gv (pick-a-stick alpha (inc idx)))))))

(defmacro dirichlet-process [tag alpha base]
  `(memo [~tag ~alpha]
	 ~base
	 (gv (pick-a-stick ~alpha 1))))

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

;;;; Test LDA

(defn indexed [coll]
  (seq (zipmap (iterate inc 0) coll)))

(defn lda [docs words topic-labels]
  (let [alphas (for [tl topic-labels] 1)
	betas (for [w words] 1)
	topics (into {}
		     (for [tl topic-labels]
		       [tl (dirichlet-cp [:topic tl] betas)]))]
    (doseq [[idx doc] (indexed docs)]
      (let [top-weights (dirichlet-cp [:doc idx] alphas)]
    	(doseq [[j w] (indexed doc)]
    	  (cond-data (discrete-cp [:word idx j]
				  (zipmap words
					  (let [top-label (discrete-cp [:label idx j]
								       (zipmap topic-labels
									       (gv top-weights)))]
					    (gv (get topics (gv top-label))))))
    		     w))))
    (det-cp :LDA
    	    (into {} (for [[tl tws] topics]
    		       [tl (zipmap words (gv tws))])))))

;; (def words [:a :b :c])

;; (def topics
;;      [(normalize (zipmap words [1 1 0]))
;;       (normalize (zipmap words [0 0 1]))])

(def words [:a :b :c :d :e :f])

(def topics
     [(normalize (zipmap words [1 1 0 0 0 0]))
      (normalize (zipmap words [0 0 1 1 0 0]))
      (normalize (zipmap words [0 0 0 0 1 1]))])

(defn generate-docs [n k topics]
  (let [alphas (for [_ topics] 1)]
    (for [_ (range n)]
      (let [top-weights (first (sample-dirichlet 2 alphas))]
	(for [_ (range k)]
	  (let [topic (sample-from (zipmap topics top-weights))
		word  (sample-from topic)]
	    word))))))

(def test-docs (generate-docs 13 42 topics))

(defn test-lda [n docs topic-labels]
  (let [words (distinct (flatten docs))]
    (loop [idx 0
	   topics (sample-traces (fn [] (lda docs words topic-labels)))]
      (if (< idx n)
	(do
	  (when (= (mod idx 10000) 0)
	    (let [data (for [tl topic-labels]
			 (let [top (get (first topics) tl)]
			   {:words (keys top)
			    :probs (vals top)
			    :topic (repeat (count top) tl)}))]
	      (view
	       (bar-chart (flatten (map :words data))
			  (flatten (map :probs data))
			  :legend true
			  :x-label "words"
			  :y-label "prob."
			  :group-by (flatten (map :topic data))))))
	  (recur (inc idx) (rest topics)))
	(first topics)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; For models with a fixed topology faster sampling should be possible
;;; if a deterministic update scheme is used and changes in the topology
;;; are not checked
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn assert-same-topology [choice-points-a choice-points-b]
  (doseq [[name cp-a] choice-points-a]
    (assert (contains? choice-points-b name))
    (let [cp-b (choice-points-b name)]
      (when-not (and (= (:dependents cp-a) (:dependents cp-b))
		     (= (:depends-on cp-a) (:depends-on cp-b)))
	(error "Topology changed: " name "!!!"))))
  true)

(defn sampling-step-fixed [choice-points selected all-dependencies]
  (with-fresh-store choice-points
    (let [selected-cp (choice-points selected)
	  change-set ;; (get all-dependencies (:name selected-cp))
	  (ordered-dependencies (:name selected-cp))
	  ;; (-> choice-points
	  ;; 	  (get (:name selected-cp))
	  ;; 	  :ordered-dependencies)
	  trace-log-lik (total-log-lik change-set)
	  
	  [prop-val fwd-log-lik bwd-log-lik]
	  (propose selected-cp (:value selected-cp))]
      (swap! *global-store*
	     assoc-in [:choice-points (:name selected-cp) :value] prop-val)
      (propagate-change-to change-set)

      (if (trace-failed?)
	[choice-points false]
	(do (let [removed-cps (remove-uncalled-choices)]
	      (when-not (empty? (-> @*global-store* :newly-created))
		(error "New choice points created during fixed sampling: "
		       (pr-str (map :name (-> @*global-store* :newly-created)))))
	      (when-not (empty? removed-cps)
		(error "Choice points deleted during fixed sampling: "
		       (pr-str (map :name removed-cps)))))
	    ;; (assert-same-topology choice-points (-> @*global-store* :choice-points))))
	    (let [prop-trace-log-lik (total-log-lik (-> @*global-store* :recomputed))]
	      (if (< (Math/log (rand))
		     (+ (- prop-trace-log-lik trace-log-lik)
			(- bwd-log-lik fwd-log-lik)))
		[(:choice-points @*global-store*) true]
		[choice-points false])))))))

;; (defn memoize-dependencies [choice-points]
;;   (with-fresh-store choice-points
;;     (reduce (fn [cps cp-name]
;; 	      (assoc-in cps [cp-name :ordered-dependencies]
;; 			(ordered-dependencies cp-name)))
;; 	    choice-points (keys choice-points))))

(defn sample-traces-fixed [prob-chunk select-update]
  (println "Trying to find a valid trace ...")
  (let [[cp choice-points] (find-valid-trace prob-chunk)
	output-name (:name cp)]
    (println "Generating update sequence ...")
    (let [update-seq  (select-update (prob-choice-dist choice-points))]
      ;; choice-points (memoize-dependencies choice-points)]
      (println "Started sampling")
      (letfn [(samples [choice-points idx accepted update-seq all-dependencies]
		(if (seq update-seq)
		  (lazy-seq
		   (let [val (if (= (:type cp) ::deterministic)
			       (:recomputed (get choice-points output-name))
			       (:value (get choice-points output-name)))
			 [next-choices accepted?]
			 (sampling-step-fixed choice-points
					      (first update-seq)
					      all-dependencies)
			 output? (= (mod idx 500) 0)
			 accepted (if accepted? (inc accepted) accepted)]
		     (when output?
		       (println idx ": " val)
		       (println "Log. lik.: " (with-fresh-store choice-points
						(total-log-lik (keys choice-points))))
		       (println "Accepted " accepted " out of last 500 samples"))
		     (cons val
			   (samples next-choices (inc idx)
				    (if output? 0 accepted)
				    (rest update-seq)
				    all-dependencies))))
		  ()))]
	;; (binding [ordered-dependencies (memoize ordered-dependencies)]
	;; general memoization not fast enough => add argument with data
	;; Memoization works, but lazy sequence generated by samples escapes
	;; the scope here!
	(samples choice-points 0 0 update-seq
		 (do (println "Caching dependencies ...")
		     (time
		      (with-fresh-store choice-points
			(into {} (for [cp-name (keys choice-points)]
				   [cp-name (ordered-dependencies cp-name)]))))))))))

(defn random-selection [n choices-dist]
  (repeatedly n (fn [] (sample-from choices-dist))))
  
(defn lda-fixed [docs words topic-labels]
  (let [alphas (for [tl topic-labels] 1)
	betas (for [w words] 1)
	topics (det-cp :topics
		 (into {}
		       (for [tl topic-labels]
			 [tl (gv (dirichlet-cp [:topic tl] betas))])))]
    (doseq [[idx doc] (indexed docs)]
      (let [top-weights (dirichlet-cp [:doc idx] alphas)]
    	(doseq [[j w] (indexed doc)]
    	  (cond-data (discrete-cp [:word idx j]
				  (zipmap words
					  (let [top-label (discrete-cp [:label idx j]
								       (zipmap topic-labels
									       (gv top-weights)))]
					    (get (gv topics) (gv top-label)))))
		     w))))
    (det-cp :LDA
    	    (into {} (for [[tl tws] (gv topics)]
    		       [tl (zipmap words tws)])))))

(declare random-selection-alias)

(defn test-lda-fixed [n-gibbs lda-model docs topic-labels]
  (let [words (distinct (flatten docs))
	n-choices (atom 0)]
    (loop [idx 0
	   topics (sample-traces-fixed (fn [] (lda-model docs words topic-labels))
				       (fn [cps] (let [ns (keys cps)]
						   (reset! n-choices (count ns))
						   ;; (take (* n-gibbs @n-choices) (cycle ns))))
						   (random-selection-alias (* n-gibbs @n-choices) cps))))]
      (if (< idx (* n-gibbs @n-choices))
	(do
	  (when (= (mod idx @n-choices) 0)
	    (println (apply str (repeat 80 "*")))
	    (println (/ idx @n-choices) " complete sampling steps of " @n-choices " choice points")
	    (println (apply str (repeat 80 "*"))))
	  (when (= (mod idx (int (Math/ceil (/ (* n-gibbs @n-choices) 10)))) 0)
	    (let [data (for [tl topic-labels]
			 (let [top (get (first topics) tl)]
			   {:words (keys top)
			    :probs (vals top)
			    :topic (repeat (count top) tl)}))]
	      (view
	       (bar-chart (flatten (map :words data))
			  (flatten (map :probs data))
			  :legend true
			  :x-label "words"
			  :y-label "prob."
			  :group-by (flatten (map :topic data))))))
	  (recur (inc idx) (rest topics)))
	(first topics)))))

;;; fast sampling using the alias method

(defn init-alias [p]
  (let [n (count p)
	{large :large, small :small}
	(group-by (fn [i] (if (> (p i) (/ 1 n))
			    :large
			    :small))
		  (range n))

	prob  (make-array Double n)
	alias (make-array Integer n)]

    (loop [p p
	   small small
	   large large]
      (if (and (seq small) (seq large))
	(let [[j & small] small
	      [k & large] large]
	  (aset prob  j (double (* n (p j))))
	  (aset alias j k)

	  (let [p (assoc p k
			 (+ (p k) (- (p j) (/ 1 n))))
		push-large? (> (p k) (/ 1 n))]
	    (recur p
		   (if push-large? small (cons k small))
		   (if push-large? (cons k large) large))))
	(do (loop [small small]
	      (when (seq small)
		(aset prob (first small) (double 1))
		(recur (rest small))))
	    (loop [large large]
	      (when (seq large)
		(aset prob (first large) (double 1))
		(recur (rest large)))))))
	  
    [n (vec (seq prob)) (vec (seq alias))]))

(defn sample-alias [n prob alias]
  (let [u (* n (rand))
	j (int u)]
    (if (<= (- u j) (prob j))
      j
      (alias j))))

(defn density [vs]
  (let [freqs (frequencies vs)
	total (reduce + (vals freqs))]
    (into {} (for [[v c] freqs] [v (float (/ c total))]))))

(defn random-selection-alias [n choices-dist]
  (repeatedly n
	      (let [vs (vec (keys choices-dist))
		    [d prob alias] (init-alias (vec (vals choices-dist)))]
		(fn [] (vs (sample-alias d prob alias))))))

(defn test-sampling [num weight-map]
  (let [pdist (normalize weight-map)]
    (time (println (density (random-selection num pdist))))
    (time (println (density (random-selection-alias num pdist))))))


(defn mixture-fixed [comp-labels data]
  (let [comp-weights (dirichlet-cp :weights (for [_ comp-labels] 10.0))
	comp-mus (det-cp :comps
			 (zipmap comp-labels
				 (for [label comp-labels] (gv (gaussian-cp [:mu label] 0.0 10.0)))))]
    (loop [points data
	   idx 0]
      (when (seq points)
	(let [comp (discrete-cp [:comp idx] (zipmap comp-labels (gv comp-weights)))]
	  ;;     mu-comp (det-cp [:mu-comp idx] (gv (get comp-mus (gv comp))))]
	  ;; (cond-data (gaussian-cp [:mu idx] (gv mu-comp) 1.0) (first points))
	  (cond-data (gaussian-cp [:mu idx] (get (gv comp-mus) (gv comp)) 1.0) (first points))
	  (recur (rest points)
		 (inc idx)))))
    (det-cp :mixture
      [(gv comp-mus)
       (gv comp-weights)])))

(defn test-mixture-fixed [comp-labels model]
  (let [data-plot (histogram data :title "Dataset" :nbins 50 :density true)
	samples  (take 500 (drop 25000 (sample-traces-fixed (fn [] (model comp-labels data))
							    ;; #(take 25500 (cycle (keys %))))))
							    (partial random-selection-alias 25500))))
	comp-mus (map first samples)
	comp-weights (map second samples)]
    (let [xs (range -12 12 0.01)
	  weights (map mean (transpose comp-weights))
	  mus (map mean (transpose (for [mus comp-mus]
				     (map #(get mus %) comp-labels))))]
      (doto data-plot
	(add-lines xs (map (fn [x] (* (nth weights 0) (pdf-normal x :mean (nth mus 0)))) xs))
	(add-lines xs (map (fn [x] (* (nth weights 1) (pdf-normal x :mean (nth mus 1)))) xs))
	(add-lines xs (map (fn [x] (* (nth weights 2) (pdf-normal x :mean (nth mus 2)))) xs))
	view)
      [weights mus])))


;;; special choice points for mixtures to implement collapsed samplers

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
	    `(fn ~args ~@body))))))
	    
(defmacro def-prob-cp [name [& params] & dist-spec]
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

(defn not-implemented [& args]
  (apply error "Not implemented: " args))

(def-prob-cp discrete-mixture-cp [component-dists mixture-dist]
  :sampler [] (->> mixture-dist
		   sample-from
		   (get component-dists)
		   sample-from)
  :calc-log-lik [x] (Math/log (reduce +
				      (for [[comp p] mixture-dist]
					(let [xp (get (get component-dists comp) x)]
					  (* p xp)))))
  :proposer [_ _] (not-implemented "discrete-mixture-cp proposer"))

(defn lda-mix-collapsed [docs words topic-labels]
  (let [alphas (for [tl topic-labels] 1)
	betas  (for [w words] 1)
	topics (det-cp :topics
		       (into {} (for [tl topic-labels]
				  [tl
				   (zipmap words
					   (gv (dirichlet-cp [:topic tl] betas)))])))]
    (doseq [[idx doc] (indexed docs)]
      (let [top-weights (dirichlet-cp [:doc idx] alphas)]
	(doseq [[j w] (indexed doc)]
	  (cond-data (discrete-mixture-cp [:word idx j]
					  (gv topics)
					  (zipmap topic-labels (gv top-weights)))
		     w))))
    (det-cp :LDA-collapsed
	    (gv topics))))

(def-prob-cp gaussian-mix-collapsed [component-means mixture-dist sdev]
  :sampler [] (let [mu (get component-means (sample-from mixture-dist))]
		(sample-normal 1 :mean mu :sd sdev))
  :calc-log-lik [x] (Math/log (reduce +
				      (for [[comp p] mixture-dist]
					(let [mu (get component-means comp)
					      xp (pdf-normal x :mean mu :sd sdev)]
					  (* p xp)))))
  :proposer [_ _] (not-implemented "gaussian-mixture-cp proposer"))

(def-prob-cp gauss-cp [mu sdev proposal-sdev]
  :sampler [] (sample-normal 1 :mean mu :sd sdev)
  :calc-log-lik [x] (Math/log (pdf-normal x :mean mu :sd sdev))
  :proposer [cp old-x]
  (let [proposal-sdev (last (:recomputed cp))
  	new-x (sample-normal 1 :mean old-x :sd proposal-sdev)]
    [new-x
     (Math/log (pdf-normal new-x :mean old-x :sd proposal-sdev))
     (Math/log (pdf-normal old-x :mean new-x :sd proposal-sdev))]))

(defn mixture-collapsed [comp-labels data]
  (let [alphas (for [_ comp-labels] 10.0)
	comp-dist (det-cp :mix (zipmap comp-labels
				       (gv (dirichlet-cp [:weights] alphas))))
	comp-means (det-cp :means
			   (zipmap comp-labels
				   (for [l comp-labels]
				     (gv (gauss-cp [:mean l] 0.0 10.0 0.1)))))]
    (doseq [[idx point] (indexed data)]
      (cond-data (gaussian-mix-collapsed [:point idx]
					 (gv comp-means)
					 (gv comp-dist)
					 1.0)
		 point))
    (det-cp :model
	    [(gv comp-means)
	     (doall (for [comp comp-labels] (get (gv comp-dist) comp)))])))