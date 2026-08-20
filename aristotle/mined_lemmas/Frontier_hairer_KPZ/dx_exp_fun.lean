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

lemma dx_exp_fun (hu : Regular u) (t : ℝ) :
    (fun y => dx (fun t x => Real.exp (u t x)) t y)
      = fun y => Real.exp (u t y) * dx u t y := by
  funext y
  exact ((hu.space t y).hasDerivAt.exp).deriv

/-- Regularity is preserved by the inverse Cole–Hopf transform `u ↦ exp u`. -/
