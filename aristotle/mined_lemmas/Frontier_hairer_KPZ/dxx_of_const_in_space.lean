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

lemma dxx_of_const_in_space (f : ℝ → ℝ) (t x : ℝ) : dx (dx (fun t _ => f t)) t x = 0 := by
  have : (fun y => dx (fun t _ => f t) t y) = fun _ => (0 : ℝ) := by
    funext y; exact dx_of_const_in_space f t y
  rw [dx, this]
  simp

/-- The spatially homogeneous KPZ equation is exactly the ODE `f' = ξ`. -/
