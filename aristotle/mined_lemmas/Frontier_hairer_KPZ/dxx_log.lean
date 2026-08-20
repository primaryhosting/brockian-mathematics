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

lemma dxx_log (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) (t x : ℝ) :
    dx (dx (fun t x => Real.log (Z t x))) t x
      = (dx (dx Z) t x * Z t x - dx Z t x * dx Z t x) / (Z t x) ^ 2 := by
  have h1 : HasDerivAt (fun y => dx Z t y) (dx (dx Z) t x) x := (hZ.space2 t x).hasDerivAt
  have h2 : HasDerivAt (fun y => Z t y) (dx Z t x) x := (hZ.space t x).hasDerivAt
  have : HasDerivAt (fun y => dx Z t y / Z t y)
      ((dx (dx Z) t x * Z t x - dx Z t x * dx Z t x) / (Z t x) ^ 2) x :=
    h1.div h2 (hpos t x).ne'
  rw [dx, dx_log_fun hpos hZ t]
  exact this.deriv

/-- Regularity is preserved by the Cole–Hopf transform `Z ↦ log Z`. -/
