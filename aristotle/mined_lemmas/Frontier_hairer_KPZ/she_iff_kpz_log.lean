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

theorem she_iff_kpz_log (xi : ℝ → ℝ → ℝ) (hpos : ∀ t x, 0 < Z t x) (hZ : Regular Z) :
    IsSHESolution xi Z ↔ IsKPZSolution xi (fun t x => Real.log (Z t x)) := by
  have key : ∀ t x, (dt Z t x = dx (dx Z) t x + Z t x * xi t x) ↔
      (dt (fun t x => Real.log (Z t x)) t x
        = dx (dx (fun t x => Real.log (Z t x))) t x
          + (dx (fun t x => Real.log (Z t x)) t x) ^ 2 + xi t x) := by
    intro t x
    have hW : Z t x ≠ 0 := (hpos t x).ne'
    rw [dt_log hpos hZ, dxx_log hpos hZ, dx_log hpos hZ]
    rw [div_eq_iff hW]
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h
      field_simp at h
      refine mul_right_cancel₀ hW ?_
      linear_combination h
  constructor
  · intro h t x; exact (key t x).1 (h t x)
  · intro h t x; exact (key t x).2 (h t x)

/-- **Inverse Cole–Hopf correspondence.**  If `u` is a regular solution of the KPZ equation,
then `exp u` solves the multiplicative stochastic heat equation. -/
