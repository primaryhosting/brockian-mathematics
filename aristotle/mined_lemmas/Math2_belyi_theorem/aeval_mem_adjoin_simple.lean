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

lemma aeval_mem_adjoin_simple (p : ℚ[X]) (x : ℂ) : aeval x p ∈ IntermediateField.adjoin ℚ {x} := by
  have hx : x ∈ ℚ⟮x⟯ := IntermediateField.mem_adjoin_simple_self ℚ x
  have h := Subalgebra.aeval_coe (R := ℚ) (A := ℂ) (S := ℚ⟮x⟯.toSubalgebra) ⟨x, hx⟩ p
  simp only at h
  rw [show ((aeval x) p) = ((aeval (⟨x, hx⟩ : ℚ⟮x⟯) p : ℚ⟮x⟯) : ℂ) by simpa using h]
  exact SetLike.coe_mem _

/-- A polynomial expression in an algebraic number is algebraic. -/
