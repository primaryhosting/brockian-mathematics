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

lemma dx_log_fun (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) (t : ℝ) :
    (fun y => dx (fun t x => Real.log (Z t x)) t y) = fun y => dx Z t y / Z t y := by
  funext y; exact dx_log hpos hZ t y

/-- Second space derivative of the Cole–Hopf transform `log Z`. -/
