import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- Cauchy–Schwarz for the Lebesgue integral on `ℝ`: for continuous, compactly supported
`u, v : ℝ → ℝ` we have `∫ |u| |v| ≤ √(∫ u²) * √(∫ v²)`. -/

theorem nirenberg_gagliardo_sup {f f' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf'c : Continuous f') (hsupp : HasCompactSupport f) (x : ℝ) :
    |f x| ≤ Real.sqrt 2 * (∫ t : ℝ, f t ^ 2) ^ ((1:ℝ)/4) * (∫ t : ℝ, f' t ^ 2) ^ ((1:ℝ)/4) := by
  set A := ∫ t : ℝ, f t ^ 2 with hAdef
  set B := ∫ t : ℝ, f' t ^ 2 with hBdef
  have hA : 0 ≤ A := integral_nonneg fun t => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun t => sq_nonneg _
  have h := nirenberg_gagliardo hderiv hf'c hsupp x
  have h1 : |f x| = Real.sqrt (f x ^ 2) := (Real.sqrt_sq_eq_abs (f x)).symm
  have h2 : Real.sqrt (f x ^ 2) ≤ Real.sqrt (2 * Real.sqrt A * Real.sqrt B) := Real.sqrt_le_sqrt h
  have h3 : Real.sqrt (2 * Real.sqrt A * Real.sqrt B)
      = Real.sqrt 2 * Real.sqrt (Real.sqrt A) * Real.sqrt (Real.sqrt B) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  have h4 : Real.sqrt (Real.sqrt A) = A ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hA]
    norm_num
  have h5 : Real.sqrt (Real.sqrt B) = B ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hB]
    norm_num
  rw [h1, ← h4, ← h5]
  exact h2.trans_eq h3

end Frontier

