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

noncomputable def momOp (hbar : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-Complex.I * hbar) • derivCLM ℂ ℂ

