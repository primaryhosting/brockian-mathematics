import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/

lemma belyi_rat_base (T : Finset ℚ) (h : T.card ≤ 2) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ t ∈ T, f.eval t = 0 ∨ f.eval t = 1) ∧
      critVal f ⊆ ({0, 1} : Set ℂ) := by
  obtain ⟨a, b, hab, hcov⟩ := exists_two_cover T h
  refine ⟨affQ a b, by rw [affQ_natDegree a b hab]; norm_num, ?_, ?_⟩
  · intro t ht
    rcases hcov t ht with rfl | rfl
    · left; rw [affQ_eval]; simp
    · right; rw [affQ_eval]; exact div_self (sub_ne_zero.mpr (Ne.symm hab))
  · rw [critVal_affQ a b hab]; exact Set.empty_subset _

/-- **Belyi reduction over `ℚ`**: any finite set of rational numbers can be mapped into
`{0,1}` by a polynomial over `ℚ` all of whose critical values also lie in `{0,1}`. -/
