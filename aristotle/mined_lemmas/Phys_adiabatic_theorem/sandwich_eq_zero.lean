/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set

namespace Phys

section Kato

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Differentiating the idempotency relation `P s * P s = P s`. -/

lemma sandwich_eq_zero {P dP : ℝ → A} (hP : ∀ s, HasDerivAt P (dP s) s)
    (hidem : ∀ s, P s * P s = P s) (s : ℝ) :
    P s * dP s * P s = 0 := by
  have h3 := leibniz_of_idempotent hP hidem s
  have h2 := hidem s
  have key : P s * dP s * P s = P s * dP s * P s + P s * dP s * P s := by
    calc P s * dP s * P s = P s * (dP s * P s + P s * dP s) * P s := by rw [h3]
      _ = (P s * dP s) * (P s * P s) + (P s * P s) * (dP s * P s) := by noncomm_ring
      _ = (P s * dP s) * P s + P s * (dP s * P s) := by rw [h2]
      _ = P s * dP s * P s + P s * dP s * P s := by noncomm_ring
  exact left_eq_add.mp key

/-- The *Kato generator* `K = P' P - P P'` of a differentiable family of idempotents
intertwines `P` with any generator commuting with `P`: writing `G = C + K` one has
`P' + P G - G P = 0`. -/
