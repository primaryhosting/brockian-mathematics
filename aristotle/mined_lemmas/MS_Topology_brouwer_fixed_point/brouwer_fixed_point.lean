import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

theorem brouwer_fixed_point {n : ℕ}
    (f : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) → (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hf : Continuous f) : ∃ x, f x = x :=
  Brouwer.brouwer_closedBall f hf

/-- **Banach fixed point theorem** (contraction mapping principle). -/
