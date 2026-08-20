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

lemma dx_log (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) (t x : ℝ) :
    dx (fun t x => Real.log (Z t x)) t x = dx Z t x / Z t x := by
  have h : HasDerivAt (fun y => Z t y) (dx Z t x) x := (hZ.space t x).hasDerivAt
  exact (h.log (hpos t x).ne').deriv

/-- The first space derivative of `log Z`, as a function of the space variable. -/
