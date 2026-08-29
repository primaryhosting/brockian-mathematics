import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open SchwartzMap Complex

/-- The position operator `X : f ↦ (x ↦ x * f x)` as a continuous linear operator on the
Schwartz space `𝓢(ℝ, ℂ)`. -/

@[simp] theorem momOp_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    momOp hbar f x = (-Complex.I * hbar) * deriv f x := by
  simp [momOp, derivCLM_apply, smul_eq_mul]

/-- Derivative of `x ↦ x * f x` for a Schwartz function `f`. -/
