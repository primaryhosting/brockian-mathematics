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

lemma critval_comp {g p : ℚ[X]} {c : ℂ}
    (h : aeval c (derivative (g.comp p)) = 0) :
    aeval c (derivative p) = 0 ∨ aeval (aeval c p) (derivative g) = 0 := by
  rw [derivative_comp, map_mul] at h
  rcases mul_eq_zero.1 h with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (by rwa [aeval_comp] at h2)

/-! ### Phase 1 : killing the irrationality of the critical values -/

/-- If all points of `S` are rational, the identity works. -/
