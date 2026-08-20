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

lemma isKPZSolution_const_in_space_iff (xi : ℝ → ℝ) (f : ℝ → ℝ) :
    IsKPZSolution (fun t _ => xi t) (fun t _ => f t) ↔ ∀ t, deriv f t = xi t := by
  constructor
  · intro h t
    have := h t 0
    rw [dxx_of_const_in_space, dx_of_const_in_space] at this
    simpa [dt] using this
  · intro h t x
    rw [dxx_of_const_in_space, dx_of_const_in_space]
    simpa [dt] using h t

/-- **Base case.**  For a continuous driving noise depending only on time, the KPZ equation has a
unique differentiable spatially homogeneous solution with any prescribed initial value; it is
given by integrating the noise. -/
