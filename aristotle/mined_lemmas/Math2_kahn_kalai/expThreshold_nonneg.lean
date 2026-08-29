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

lemma expThreshold_nonneg {F : Finset (Finset α)} (hnu : F ≠ Finset.univ)
    (hinc : Increasing F) : 0 ≤ expThreshold F := by
  have hempty : (∅ : Finset α) ∉ F := by
    intro hmem
    exact hnu (Finset.eq_univ_of_forall fun U =>
      hinc ∅ hmem U (Finset.empty_subset U))
  have h0 : IsSmall (0 : ℝ) F := by
    refine ⟨F, Covers.refl F, ?_⟩
    have : cost (0 : ℝ) F = 0 := by
      rw [cost]
      refine Finset.sum_eq_zero fun S hS => ?_
      have hSne : S.card ≠ 0 := by
        intro hc
        exact hempty (Finset.card_eq_zero.1 hc ▸ hS)
      exact zero_pow hSne
    rw [this]; norm_num
  exact le_csSup ⟨1, fun x hx => hx.2.1⟩ ⟨le_rfl, zero_le_one, h0⟩

