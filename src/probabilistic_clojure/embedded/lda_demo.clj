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
  probabilistic-clojure.embedded.lda_demo
  (:use [probabilistic-clojure.embedded.api :only (det-cp gv cond-data memo metropolis-hastings-sampling)]
	[probabilistic-clojure.utils.stuff :only (indexed)]
	[probabilistic-clojure.utils.sampling :only (sample-from normalize density)]
	[probabilistic-clojure.embedded.choice-points
	 :only (dirichlet-cp log-pdf-dirichlet discrete-cp log-pdf-discrete)]

	[incanter.core   :only (view sqrt)]
	[incanter.stats  :only (sample-dirichlet sample-multinomial sample-uniform)])
  (:import [java.awt Color Graphics Dimension]
	   [java.awt.image BufferedImage]
	   [javax.swing JPanel JFrame]))


(in-ns 'probabilistic-clojure.embedded.lda_demo)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Here we want to show the picture example from the LDA paper
;;; "Finding scientific topics" by D. Blei et al.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Basic definitions and the LDA model as a probabilistic program

(def alpha 1)
(def beta  1)

(defn lda-model [topic-labels documents]
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
						      

;;; Now generate example documents with the bar-like topics from the paper

(def xy-dim 2)

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
    (sample-document (sample-uniform 1 :min 33 :max 44 :integers true) theta topics)))

(def demo-docs (train-data 55 (topics)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; UI ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;pixels per world cell
(def scale 25)

(def topic-labels  (map (partial str "T") (range num-topics)))
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

(defn run [num skip]
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
      (. panel (repaint)))))

  ;; (dorun
  ;;  (for [[i state] (indexed (take num (em-states data)))]
  ;;    (let []
  ;;      (println i)
  ;;      (when (= (mod i skip) 0)
  ;; 	 (dosync
  ;; 	  (dorun
  ;; 	   (for [[[t w] c] (:counts (:ctw state))]
  ;; 	     (ref-set (nth topic-samples t)
  ;; 		      (assoc @(nth topic-samples t) w
  ;; 			     (omega state t w))))))
  ;; 	 (. panel (repaint))))))
  ;; :done)
