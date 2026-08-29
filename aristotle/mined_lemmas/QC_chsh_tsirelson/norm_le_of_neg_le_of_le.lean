/-
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QC

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a unital C⋆-algebra, a self-adjoint element `a` bounded above by `r` and below by `-r`
(in the C⋆-order) has norm at most `r`. -/

theorem norm_le_of_neg_le_of_le {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r)
    (h₁ : a ≤ algebraMap ℝ A r) (h₂ : -a ≤ algebraMap ℝ A r) : ‖a‖ ≤ r := by
  obtain (hsub | hnt) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim a 0] using hr
  · rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
    · exact (le_algebraMap_iff_spectrum_le (a := a) ha).mp h₁ ‖a‖ h
    · have hmem : ‖a‖ ∈ spectrum ℝ (-a) := by
        rw [← spectrum.neg_eq]
        simpa using h
      exact (le_algebraMap_iff_spectrum_le (a := -a) ha.neg).mp h₂ ‖a‖ hmem

/-- The `ℝ`-star-module structure on a C⋆-algebra, obtained by restricting scalars from `ℂ`. -/
instance : StarModule ℝ A where
  star_smul r a := by
    rw [show (star r : ℝ) = r from rfl, ← algebraMap_smul ℂ r a,
      ← algebraMap_smul ℂ r (star a), star_smul]
    simp

end CStar

/-- The negation of the first pair of observables of a CHSH tuple is again a CHSH tuple. -/
