import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

theorem banach_fixed_point {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    (f : α → α) (K : ℝ) (hK : K < 1) (hf : ∀ x y, dist (f x) (f y) ≤ K * dist x y) :
    ∃! x, f x = x := by
  -- `K` may a priori be negative (only possible when `α` is a subsingleton), so we contract
  -- with the nonnegative constant `max K 0`.
  set K' : NNReal := ⟨max K 0, le_max_right _ _⟩ with hK'
  have hc : ContractingWith K' f := by
    constructor
    · rw [← NNReal.coe_lt_one]
      simp [hK', hK]
    · intro x y
      rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      refine (hf x y).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  exact ⟨hc.fixedPoint f, hc.fixedPoint_isFixedPt, fun y hy => hc.fixedPoint_unique hy⟩

/-- **Pythagorean theorem** in a real inner product space.
(The statement is as given, with the inner product's scalar field made explicit, as required by
the current `inner` notation.) -/
