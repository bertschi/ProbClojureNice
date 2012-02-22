(ns
    ^{:author "Nils Bertschinger"
      :doc "Tests for probabilistic-clojure.embedded.
Approximate tests for the sampling related stuff"}
  probabilistic-clojure.embedded.test-sampling
  (:use clojure.test)
  (:use probabilistic-clojure.embedded.api
	probabilistic-clojure.embedded.choice-points
	probabilistic-clojure.embedded.demos
	probabilistic-clojure.utils.sampling))

(in-ns 'probabilistic-clojure.embedded.test-sampling)

(defn info-fixture [tests]
  (binding [*info-steps* 2500]
    (tests)))

(use-fixtures :once info-fixture)

(defn sample-bayes-net [steps bayes-net sampler]
  (->> (sampler bayes-net)
       (drop (/ steps 4))
       (take steps)
       density))

(defn retracts-net
  "Example of a changing topology -- choice points are removed and re-created --
to test dependency tracking and sampling."
  []
  (let [root       (flip-cp :root  0.5)
	path-left  (flip-cp :left  (do (gv root) 0.5))
	path-right (flip-cp :right (do (gv root) 0.5))]
    (det-cp :result
      (if (gv root)
	[:left  (gv path-left)]
	[:right (gv path-right)]))))

(defn prob= [x y]
  (let [eps  0.01
	diff (- x y)]
    (< (- eps) diff eps)))

(deftest retracts-sampling
  (is (prob= (get (sample-bayes-net 10000 retracts-net monte-carlo-sampling)
		  [:left false])
	     0.25))
  (is (prob= (get (sample-bayes-net 10000 retracts-net metropolis-hastings-sampling)
		  [:left false])
	     0.25)))
  
(deftest grass-demos
  (let [true-prob (float 1419/3029)]
    ;; The exact prob. of the grass net being true was calculated with the prob. monad
    (are [sampler bayes-net]
	 (prob= (get (sample-bayes-net 10000 bayes-net sampler) true) true-prob)
	 
	 monte-carlo-sampling         grass-bayes-net
	 metropolis-hastings-sampling grass-bayes-net
	 monte-carlo-sampling         grass-bayes-net-fixed
	 metropolis-hastings-sampling grass-bayes-net-fixed)))