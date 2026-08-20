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

lemma dt_log (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) (t x : ℝ) :
    dt (fun t x => Real.log (Z t x)) t x = dt Z t x / Z t x := by
  have h : HasDerivAt (fun s => Z s x) (dt Z t x) t := (hZ.time t x).hasDerivAt
  exact (h.log (hpos t x).ne').deriv

/-- Space derivative of the Cole–Hopf transform `log Z`. -/
