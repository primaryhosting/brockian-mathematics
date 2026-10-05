/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open Complex

/-- The position operator `X : f ↦ (x ↦ x · f x)` acting on complex-valued
functions of a real variable. -/

noncomputable def P (hbar : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -Complex.I * hbar * deriv f x

/-- Derivative of `y ↦ y * f y` for a Schwartz function `f`. -/
