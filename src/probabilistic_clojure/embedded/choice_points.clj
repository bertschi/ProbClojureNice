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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Probabilistic programming using constraint propagation
;;;; to efficiently track dependencies between choice points
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ns
    ^{:author "Nils Bertschinger"
      :doc "Part of probabilistic-clojure.embedded which implements a couple
of probabilistic choice points."}
  probabilistic-clojure.embedded.choice-points
  (:use [probabilistic-clojure.embedded.api :only (def-prob-cp)]
	[probabilistic-clojure.utils.stuff :only (ensure-list error)]))

(def-prob-cp flip-cp [p]
  :sampler [] (< (rand) p)
  :calc-log-lik [b] (Math/log (if x p (- 1 p)))
  ;; proposer returns a vector of [new-value forward-log-prob backward-log-prob]
  :proposer [b0] [(not b0) 0 0])