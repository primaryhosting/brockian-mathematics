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

@[simp] theorem posOp_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : posOp f x = (x : ℂ) * f x := by
  simp [posOp, smulLeftCLM_apply_apply Function.Complex.hasTemperateGrowth_ofReal,
    smul_eq_mul]

