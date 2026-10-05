import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma muFail_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (H : Finset (Finset α)) :
    muFail b H ≤ muFail a H := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  have ha1 : a < 1 := lt_of_lt_of_le hlt hb
  set r : ℝ := (b - a) / (1 - a) with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by linarith)]
    linarith
  have hne : (1 : ℝ) - a ≠ 0 := by linarith
  have hkey : 1 - (1 - a) * (1 - r) = b := by
    rw [hr]
    field_simp
    ring
  have h1 : muFail b H = ∑ W : Finset α, ∑ V : Finset α,
      weight a W * weight r V * failInd H (W ∪ V) := by
    rw [sum_union_weight, hkey, muFail]
  rw [h1, muFail]
  calc ∑ W : Finset α, ∑ V : Finset α, weight a W * weight r V * failInd H (W ∪ V)
      ≤ ∑ W : Finset α, ∑ V : Finset α, weight a W * weight r V * failInd H W := by
        refine Finset.sum_le_sum fun W _ => Finset.sum_le_sum fun V _ => ?_
        refine mul_le_mul_of_nonneg_left (failInd_anti Finset.subset_union_left) ?_
        exact mul_nonneg (weight_nonneg ha (by linarith) W) (weight_nonneg hr0 hr1 V)
    _ = ∑ W : Finset α, weight a W * failInd H W := by
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_weight, mul_one]

/-- The number of halving rounds needed for an `ℓ`-bounded hypergraph. -/
