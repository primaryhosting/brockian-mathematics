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

noncomputable def momCLM (hbar : ℝ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (-Complex.I * hbar) • SchwartzMap.derivCLM ℂ ℂ

/-- Derivative of `y ↦ f y * y` for a Schwartz function `f`. -/
