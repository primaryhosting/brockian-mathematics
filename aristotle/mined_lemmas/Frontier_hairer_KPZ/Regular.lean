/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-! ## Space-time functions and partial derivatives

A space-time function is modelled as `u : ℝ → ℝ → ℝ`, where `u t x` is its value at time `t`
and space point `x`. -/

/-- Time derivative of a space-time function. -/

lemma Regular.exp (hu : Regular u) : Regular (fun t x => Real.exp (u t x)) where
  time t x := ((hu.time t x).hasDerivAt.exp).differentiableAt
  space t x := ((hu.space t x).hasDerivAt.exp).differentiableAt
  space2 t x := by
    rw [dx_exp_fun hu t]
    exact (((hu.space t x).hasDerivAt.exp).mul (hu.space2 t x).hasDerivAt).differentiableAt

/-- **Cole–Hopf correspondence.**  For a positive, regular space-time function `Z`, the function
`Z` solves the multiplicative stochastic heat equation `∂ₜ Z = ∂ₓ² Z + Z ξ` if and only if its
logarithm solves the KPZ equation `∂ₜ u = ∂ₓ² u + (∂ₓ u)² + ξ`. -/
