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

lemma leibniz_of_idempotent {P dP : ℝ → A} (hP : ∀ s, HasDerivAt P (dP s) s)
    (hidem : ∀ s, P s * P s = P s) (s : ℝ) :
    dP s * P s + P s * dP s = dP s := by
  have h1 : HasDerivAt (fun t => P t * P t) (dP s * P s + P s * dP s) s := (hP s).mul (hP s)
  have h2 : HasDerivAt (fun t => P t * P t) (dP s) s := by
    have h : (fun t => P t * P t) = P := funext hidem
    rw [h]; exact hP s
  exact h1.unique h2

/-- For a differentiable family of idempotents one has `P * P' * P = 0`. -/
