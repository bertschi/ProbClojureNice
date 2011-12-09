;;; These old sampling routines are now replaced by metropolis-hastings-sampling

;;; The actual Metropolis Hastings sampling

(defn sampling-step [choice-points]
  (with-fresh-store choice-points
    (let [prob-choices (prob-choice-dist choice-points)
	  selected-cp (choice-points (sample-from prob-choices))
	  change-set (ordered-dependencies (:name selected-cp) choice-points)
	  trace-log-lik (total-log-lik change-set choice-points)
	  
	  [prop-val fwd-log-lik bwd-log-lik]
	  (propose selected-cp (:value selected-cp))]
      ;; (println "Proposing: " (:name selected-cp) ": " change-set)
      ;; (do (println :OLD) (doseq [cp (vals choice-points)] (println (probabilistic-clojure.embedded.tests/cp-str cp))))
      (assoc-in-store! [:choice-points (:name selected-cp) :value]
		       prop-val)
      (propagate-change-to change-set)
      (if (trace-failed?)
	choice-points
	(let [;; _ (do (println :NEW) (doseq [cp (vals (fetch-store :choice-points))] (println (probabilistic-clojure.embedded.tests/cp-str cp))))
	      _ (assert (clojure.set/subset? (set change-set) (fetch-store :recomputed)))
	      _ (assert (= (fetch-store :recomputed) (union (set change-set) (fetch-store :newly-created)))
			(println "Aha " (str [(fetch-store :recomputed) (set change-set) (fetch-store :newly-created)])))
	      removed-cps (remove-uncalled-choices)
	      ;; _ (do (println :CLEAN) (doseq [cp (vals (fetch-store :choice-points))] (println (probabilistic-clojure.embedded.tests/cp-str cp))))
	      _ (assert (empty? (clojure.set/intersection removed-cps (fetch-store :newly-created))))
	      _ (let [new (set (keys (fetch-store :choice-points)))
		      old (set (keys choice-points))]
		  (assert (and (= new (difference (union old (fetch-store :newly-created))
						  removed-cps))
			       (= old (difference (union new removed-cps) (fetch-store :newly-created))))
			  [old (fetch-store :newly-created) removed-cps new]))
										
	      trace-log-lik (total-log-lik (union (set change-set) removed-cps)
					   ;; (keys choice-points)
					   ;; (difference (fetch-store :recomputed) (fetch-store :newly-created))
					   choice-points)
	      prop-trace-log-lik (total-log-lik ;; (keys (fetch-store :choice-points))
				  (difference (fetch-store :recomputed) removed-cps)
				  (fetch-store :choice-points))
	      
	      fwd-trace-log-lik (total-log-lik (fetch-store :newly-created) (fetch-store :choice-points))
	      bwd-trace-log-lik (total-log-lik removed-cps choice-points)
	      ;; prop-trace-log-lik (total-log-lik (difference
	      ;; 					 ;; TODO: What about reweighting of reused choice-points???
	      ;; 					 ;; (union (set change-set) (-> @*global-store* :newly-created))
	      ;; 					 (fetch-store :recomputed))
	      ;; 					 ;; removed-cps
	      ;; 					(fetch-store :choice-points))
	      prop-prob-choices (prob-choice-dist (fetch-store :choice-points))]
	  ;; (when-not (empty? (clojure.set/intersection (fetch-store :recomputed) removed-cps))
	  ;;   (print "."))
	  ;; (when-let [it (seq removed-cps)] (println "Removed: " (pr-str (map :name it)) " (" (count it) ")"))
	  ;; (when-let [it (seq (fetch-store :newly-created))] (println  "Created: " it " (" (count it) ")"))
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
		       (pr-str (fetch-store :newly-created))))
	      (when-not (empty? removed-cps)
		(error "Choice points deleted during fixed sampling: "
		       (pr-str removed-cps))))
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

