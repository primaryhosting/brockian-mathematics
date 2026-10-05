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

noncomputable def posCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    Function.Complex.hasTemperateGrowth_ofReal

/-- The momentum operator `-i ℏ d/dx` as a continuous linear endomorphism of
`𝓢(ℝ, ℂ)`. -/
