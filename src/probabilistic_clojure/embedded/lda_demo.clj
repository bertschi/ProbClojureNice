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
      :doc "Part of probabilistic-clojure.embedded. Demo of Latent Dirichlet Allocation."}
  probabilistic-clojure.embedded.lda-demo
  (:use [probabilistic-clojure.embedded.api :only (det-cp gv cond-data memo metropolis-hastings-sampling def-prob-cp trace-failure)]
	[probabilistic-clojure.utils.stuff :only (indexed)]
	[probabilistic-clojure.embedded.choice-points
	 :only (dirichlet-cp log-pdf-dirichlet *dirichlet-initial-factor* discrete-cp)]
	 
	[incanter.core   :only (view sqrt)]
	[incanter.stats  :only (sample-dirichlet sample-multinomial sample-uniform sample-gamma pdf-gamma sample-normal pdf-normal)])
  (:import [java.awt Color Graphics Dimension]
	   [java.awt.image BufferedImage]
	   [javax.swing JPanel JFrame]
           [org.apache.commons.math.special Gamma]))

(in-ns 'probabilistic-clojure.embedded.lda-demo)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Here we want to show the picture example from the LDA paper
;;; "Finding scientific topics" by D. Blei et al.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Basic definitions and the LDA model as a probabilistic program

(def alpha 1)
(def beta  1)

(defn lda [topic-labels documents]
  (let [words (distinct (apply concat documents))
	num-topics (count topic-labels)
	alphas (repeat (count words) alpha)
	betas  (repeat num-topics    beta)]
    (doseq [[i doc] (indexed documents)]
      (let [topic-weights (dirichlet-cp [:weights i] betas)]
	;; now for each word draw a topic and condition on the observed word
	(doseq [[j word] (indexed doc)]
	  (let [assigned (discrete-cp [:assign i j]
				      (zipmap topic-labels (gv topic-weights)))
		topic-dist (memo [:topic i j] (dirichlet-cp :weights alphas) (gv assigned))]
	    (cond-data (discrete-cp [:word i j]
				    (zipmap words (gv topic-dist)))
		       word)))))
    (det-cp :lda
	    (doall
	     (into {}
		   (for [tl topic-labels]
		     [tl
		      (zipmap words
			      (gv (memo [:topic tl]
					(dirichlet-cp :weights alphas) tl)))]))))))
						      

;;; Collapsing out the topic assignments should be faster

;; A collapsed mixture choice point that takes contigency counts as
;; data (usually much faster than the one in demo.clj)
(def-prob-cp collapsed-mixture-cp [comp-probs comp-models]
  :sampler [] [] ; just a dummy initialization ... no data drawn from model
  :calc-log-lik [counts]
  (let [sum (partial reduce +)]
    (sum (for [[x c] counts]
	   (* c
              (Math/log ; switch to log-probabilities
               (sum (for [[p cm] (zipmap comp-probs comp-models)]
                      ;; component model is a function that calculates the
                      ;; probability for a given datapoint
                      (* p (cm x)))))))))
  :proposer [_] (probabilistic-clojure.utils.stuff/error
		 "collapsed-mixture-cp does not implement a proposer!"))

(defn lda-collapsed [topic-labels documents]
  (let [words (distinct (apply concat documents))
	num-topics (count topic-labels)
	alphas (repeat (count words) alpha)
	betas  (repeat num-topics    beta)

	topic-dists (for [tl topic-labels]
		      (dirichlet-cp [:topic tl] alphas))]
    (doseq [[i doc] (indexed documents)]
      (let [topic-weights (dirichlet-cp [:weights i] betas)
	    topic-models  (det-cp [:models i]
				  (doall (for [w-probs topic-dists]
					   (let [w-dist (zipmap words (gv w-probs))]
					     (fn [word] (get w-dist word))))))]
	(cond-data (collapsed-mixture-cp [:doc i]
					 (gv topic-weights) (gv topic-models))
		   (frequencies doc))))
    (det-cp :lda-collapsed
	    (into {}
		  (for [[tl top] (zipmap topic-labels topic-dists)]
		    [tl (zipmap words (gv top))])))))
						  
;;; Now generate example documents with the bar-like topics from the paper

(def xy-dim 3)

(def num-topics (* 2 xy-dim))
(def num-words  (* xy-dim xy-dim))

(defn row-or-col-topic [row-or-col]
  (let [row (:row row-or-col), col (:col row-or-col)]
    (for [x (range xy-dim), y (range xy-dim)
	  :when (or (and row (= row x)) (and col (= col y)))]
      [x y])))

(defn topics []
  "Create topics corresponding to horizontal and vertical images.
Each topic is a sequence of words that can appear in this topic."
  (concat (for [row (range xy-dim)] (row-or-col-topic {:row row}))
	  (for [col (range xy-dim)] (row-or-col-topic {:col col}))))

(defn sample-document [nwords theta topics]
  (let [assigned (sample-multinomial nwords :probs theta)
	wprobs (for [_ (range xy-dim)] (/ 1 xy-dim))]
    (map (fn [z wi] (nth (nth topics z) wi))
	 assigned (sample-multinomial nwords :probs wprobs))))

(defn train-data [n topics]
  (for [theta (sample-dirichlet n (repeat (count topics) beta))]
    ;; (sample-document (sample-uniform 1 :min 33 :max 44 :integers true) theta topics)))
    (sample-document 250 theta topics)))
    
;; (def demo-docs (train-data 55 (topics)))
(def demo-docs (train-data 120 (topics)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; UI ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;pixels per world cell
(def scale 25)

(def topic-labels  (doall (map (partial str "T") (range num-topics))))
(def topic-samples (into {} (for [tl topic-labels] [tl (ref {})])))

(defn fill-cell [#^Graphics g x y c]
  (doto g
    (.setColor c)
    (.fillRect (* x scale) (* y scale) scale scale)))

(defn render [g]
  (let [v (dosync (doall
		   (for [z topic-labels]
		     (apply vector (for [x (range xy-dim) y (range xy-dim)] 
				     (get @(get topic-samples z) [x y] 0))))))
	img (new BufferedImage (* (+ num-topics 2) scale xy-dim) (* scale xy-dim) 
                 (. BufferedImage TYPE_INT_ARGB))
        bg (. img (getGraphics))]
    (doto bg
      (.setColor (. Color blue))
      (.fillRect 0 0 (. img (getWidth)) (. img (getHeight))))
    (dorun 
     (for [z (range num-topics) x (range xy-dim) y (range xy-dim)]
       (let [rgb (max 0 (- 255 (int (* xy-dim 255 ((nth v z) (+ (* x xy-dim) y))))))]
	 (fill-cell bg (+ x (* z (inc xy-dim))) y (Color. rgb rgb rgb)))))
    (. g (drawImage img 0 0 nil))
    (. bg (dispose))))

(def panel (doto (proxy [JPanel] []
                        (paint [g] (render g)))
             (.setPreferredSize (new Dimension 
                                     (* (+ num-topics 2) scale xy-dim) 
                                     (* scale xy-dim)))))

(def frame (doto (new JFrame) (.add panel) .pack .show))

(defn run [num skip lda-model]
  (binding [*dirichlet-initial-factor* 50]
    (doseq [[i tops] (indexed
		      (take num
			    (metropolis-hastings-sampling
			     (fn []
			       (lda-model topic-labels demo-docs)))))]
      (when (= (mod i skip) 0)
	(dosync
	 (doseq [tl topic-labels]
	   (ref-set (get topic-samples tl)
		    (get tops tl))))
	(. panel (repaint))))))

;;; Dirichlet choice point based on Gamma samples => more local
;;; proposal distribution

(defn diri-probs [gammas]
  (let [total (reduce + gammas)]
    (vec (map #(/ % total) gammas))))

(defn propose-gamma-prior [old-x shape rate]
  ;; propose new value from Gamma prior
  (let [new-x (sample-gamma 1 :shape shape :rate rate)]
    [new-x
     (Math/log (pdf-gamma new-x :shape shape :rate rate))
     (Math/log (pdf-gamma old-x :shape shape :rate rate))]))

(defn propose-gamma-normal [old-x shape sdev-factor]
  (let [sdev  (* shape sdev-factor)
        new-x (sample-normal 1 :mean old-x :sd sdev)]
    (when (< new-x 0)
      (trace-failure))
    [new-x
     (Math/log (pdf-normal new-x :mean old-x :sd sdev))
     (Math/log (pdf-normal old-x :mean new-x :sd sdev))]))

(defn propose-gamma-log-normal [old-x sdev]
  (let [log-old-x (Math/log old-x)
        log-new-x (sample-normal 1 :mean log-old-x :sd sdev)]
    [(Math/exp log-new-x)
     (Math/log (pdf-normal log-new-x :mean log-old-x :sd sdev))
     (Math/log (pdf-normal log-old-x :mean log-new-x :sd sdev))]))

;; un-normalized Dirichlet distribution
(def-prob-cp dirichlet-cp-gamma [alphas]
  :sampler [] (vec (for [a alphas] (sample-gamma 1 :shape a :rate 1)))
  :calc-log-lik [gs] (log-pdf-dirichlet (diri-probs gs) alphas)
  :proposer [old-gs] (let [idx (rand-int (count old-gs))
                           [new-g fwd bwd]
                           ;; (propose-gamma-prior (nth old-gs idx) (nth alphas idx) 1)]
                           (propose-gamma-normal (nth old-gs idx) (nth alphas idx) 1)]
                           ;; (propose-gamma-log-normal (nth old-gs idx) 1)]
                       [(assoc old-gs idx new-g) fwd bwd]))

(defn lda-collapsed-gamma [topic-labels documents]
  (let [words (distinct (apply concat documents))
	num-topics (count topic-labels)
	alphas (repeat (count words) alpha)
	betas  (repeat num-topics    beta)

	topic-dists (for [tl topic-labels]
		      (dirichlet-cp-gamma [:topic tl] alphas))]
    (doseq [[i doc] (indexed documents)]
      (let [topic-weights (dirichlet-cp-gamma [:weights i] betas)
	    topic-models  (det-cp [:models i]
				  (doall (for [w-probs topic-dists]
					   (let [w-dist (zipmap words (diri-probs (gv w-probs)))]
					     (fn [word] (get w-dist word))))))]
	(cond-data (collapsed-mixture-cp [:doc i]
					 (diri-probs (gv topic-weights)) (gv topic-models))
		   (frequencies doc))))
    (det-cp :lda-collapsed
	    (into {}
		  (for [[tl top] (zipmap topic-labels topic-dists)]
		    [tl (zipmap words (diri-probs (gv top)))])))))

(def-prob-cp gamma-cp [shape rate]
  :sampler [] (sample-gamma 1 :shape shape :rate rate)
  :calc-log-lik [x]
  (Math/log (pdf-gamma x :shape shape :rate rate))
  :proposer [old-x]
  (propose-gamma-log-normal old-x 1))