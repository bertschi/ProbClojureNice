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

(defn make-det-cp [name whole body]
  (make-choice-point name ::deterministic whole body))

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

(defn update-dependencies [cp-name]
  (let [caller-name (current-caller)]
    (when caller-name
      (update-in-store! [:choice-points caller-name :depends-on]
			conj cp-name)
      (update-in-store! [:choice-points cp-name :dependents]
			conj caller-name))))

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


