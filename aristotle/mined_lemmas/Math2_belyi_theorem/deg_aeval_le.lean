import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma deg_aeval_le {x : ℂ} (hx : IsIntegral ℚ x) (p : ℚ[X]) : deg (aeval x p) ≤ deg x := by
  have hiy : IsIntegral ℚ (aeval x p) := isIntegral_aeval hx p
  haveI : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
  have hle : ℚ⟮aeval x p⟯ ≤ ℚ⟮x⟯ := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact aeval_mem_adjoin_simple p x
  have h2 := finrank_le_of_le_right hle
  rw [IntermediateField.adjoin.finrank hx, IntermediateField.adjoin.finrank hiy] at h2
  exact h2

/-- A root of a nonzero rational polynomial is algebraic. -/
