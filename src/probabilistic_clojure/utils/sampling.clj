(ns
    ^{:author "Nils Bertschinger"
      :doc "Utility functions for discrete probability distributions."}
  probabilistic-clojure.utils.sampling)


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

;;; fast sampling using the alias method

(defn init-alias
  "Takes a vector of probabilities and initializes the \"magic\" arrays
prob and alias used by the alias method."
  [p]
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

(defn sample-alias
  "Draws one sample using the alias method. n denotes the length of the vectors prob and alias."
  [n prob alias]
  (let [u (* n (rand))
	j (int u)]
    (if (<= (- u j) (prob j))
      j
      (alias j))))

;;; Lazy streams of random draws

(defn random-selection
  "Returns a lazy sequence of random draws from dist. Optionally the requested
number of samples can be specified."
  ([dist]
     (repeatedly (fn [] (sample-from dist))))
  ([n dist]
     (repeatedly n (fn [] (sample-from dist)))))

(defn random-selection-alias
  "Returns a lazy sequence of random draws from dist using the alias method (very fast if a large
number of samples is required). Optionally the requested number of samples can be specified."
  ([dist]
     (repeatedly (let [vs (vec (keys dist))
		       [n prob alias] (init-alias (vec (vals dist)))]
		   (fn [] (vs (sample-alias n prob alias))))))
  ([n dist]
     (take n (random-selection-alias dist))))

;;; Distribution utilities

(defn normalize
  "Normalize the distribution given by the hash-map dist"
  [dist]
  (let [total (reduce + (vals dist))]
    (if (= total 1)
      dist
      (into {} (for [[x p] dist] [x (/ p total)])))))

(defn density
  "Like frequencies, but normalizes the counts."
  [vs]
  (let [freqs (frequencies vs)
	total (reduce + (vals freqs))]
    (into {} (for [[v c] freqs] [v (double (/ c total))]))))


