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

def IsKPZSolution (xi u : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, dt u t x = dx (dx u) t x + (dx u t x) ^ 2 + xi t x

/-- `Z` solves the multiplicative stochastic heat equation `∂ₜ Z = ∂ₓ² Z + Z ξ` driven by `xi`. -/
