/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-! ## Euclidean 3-space as `ℝ × ℝ × ℝ`

We use the plain product type and equip it with an explicit dot product and cross
product, so that all differential-geometric quantities below are literally the
classical ones. -/

/-- Ambient space `ℝ³`. -/
abbrev E3 := ℝ × ℝ × ℝ

/-- The Euclidean dot product on `ℝ³`. -/

theorem hasDerivAt_willmorePrimitive (R r : ℝ) (hr : 0 < r) (hR : r < R) (u : ℝ) :
    HasDerivAt (willmorePrimitive R r)
      ((R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u))) u := by
  set S := Real.sqrt (R ^ 2 - r ^ 2) with hSdef
  have hr0 : (0:ℝ) < R := hr.trans hR
  have hS0 : 0 < S := Real.sqrt_pos.2 (by nlinarith)
  have hSsq : S ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have hcos : -1 ≤ Real.cos u := Real.neg_one_le_cos u
  have hcos' : Real.cos u ≤ 1 := Real.cos_le_one u
  have hD : 0 < R + r * Real.cos u := by nlinarith
  have hM : 0 < R + S + r * Real.cos u := by nlinarith
  have hRS : (0:ℝ) < R + S := by nlinarith
  have hnum : HasDerivAt (fun t => r * Real.sin t) (r * Real.cos u) u := by
    simpa using (Real.hasDerivAt_sin u).const_mul r
  have hden : HasDerivAt (fun t => R + S + r * Real.cos t) (-(r * Real.sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add (R + S)
  have hq : HasDerivAt (fun t => r * Real.sin t / (R + S + r * Real.cos t))
      ((r * Real.cos u * (R + S + r * Real.cos u) - r * Real.sin u * -(r * Real.sin u))
        / (R + S + r * Real.cos u) ^ 2) u := hnum.div hden (ne_of_gt hM)
  have hat := hq.arctan
  have h := (Real.hasDerivAt_sin u).add
    ((((hasDerivAt_id u).sub (hat.const_mul 2)).const_mul (R ^ 2)).div_const (4 * r * S))
  refine h.congr_deriv ?_
  have hpyth : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
  have hMne : (R + S + r * Real.cos u) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hM)
  have hDne : R + r * Real.cos u ≠ 0 := ne_of_gt hD
  have h1 : 1 + (r * Real.sin u / (R + S + r * Real.cos u)) ^ 2
      = 2 * (R + S) * (R + r * Real.cos u) / (R + S + r * Real.cos u) ^ 2 := by
    field_simp
    linear_combination r ^ 2 * hpyth + hSsq
  have h2 : r * Real.cos u * (R + S + r * Real.cos u) - r * Real.sin u * -(r * Real.sin u)
      = r * Real.cos u * (R + S) + r ^ 2 := by
    linear_combination r ^ 2 * hpyth
  have key : 1 - 2 * (1 / (1 + (r * Real.sin u / (R + S + r * Real.cos u)) ^ 2) *
      ((r * Real.cos u * (R + S + r * Real.cos u) - r * Real.sin u * -(r * Real.sin u))
        / (R + S + r * Real.cos u) ^ 2)) = S / (R + r * Real.cos u) := by
    rw [h1, h2, div_mul_div_comm, one_mul, div_mul_cancel₀ _ hMne]
    field_simp
    linear_combination -hSsq
  rw [key]
  have hne : (4:ℝ) * r * (R + r * Real.cos u) ≠ 0 := by positivity
  have hstep : R ^ 2 * (S / (R + r * Real.cos u)) / (4 * r * S)
      = R ^ 2 / (4 * r * (R + r * Real.cos u)) := by
    rw [div_eq_div_iff (by positivity) hne, mul_comm (R ^ 2) (S / (R + r * Real.cos u)),
      mul_assoc, div_mul_eq_mul_div, div_eq_iff hDne]
    ring
  rw [hstep, eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
  ring

/-- The Willmore integrand of the torus of revolution is continuous. -/
