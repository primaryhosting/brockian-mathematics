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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- A `C¹` function on `ℝ` with compact support is bounded (twice over) by the `L¹` norm of its
derivative:  `2 * |v x| ≤ ∫ |v'|`.  This is the one-dimensional base case of the
Gagliardo–Nirenberg–Sobolev inequality. -/

theorem two_mul_abs_le_integral_abs_deriv {v v' : ℝ → ℝ} (hv' : Continuous v')
    (hd : ∀ x, HasDerivAt v (v' x) x) (hs : HasCompactSupport v) (x : ℝ) :
    2 * |v x| ≤ ∫ t, |v' t| := by
  have hvcont : Continuous v := Differentiable.continuous fun y => (hd y).differentiableAt
  -- the derivative also has compact support
  have hderiv_eq : deriv v = v' := funext fun y => (hd y).deriv
  have hs' : HasCompactSupport v' := hderiv_eq ▸ hs.deriv
  have hint : Integrable (fun t => |v' t|) := by
    exact (hv'.abs).integrable_of_hasCompactSupport hs'.abs
  obtain ⟨R, hR0, hR⟩ := hs.exists_pos_le_norm
  set S : ℝ := max R (|x| + 1) with hS
  have hSR : R ≤ S := le_max_left _ _
  have hSx : |x| + 1 ≤ S := le_max_right _ _
  have hvL : v (-S) = 0 := by
    apply hR
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hR0 hSR)]
    exact hSR
  have hvR : v S = 0 := by
    apply hR
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hR0 hSR)]
    exact hSR
  have hii : ∀ a b : ℝ, IntervalIntegrable v' MeasureTheory.volume a b :=
    fun a b => (hv'.intervalIntegrable a b)
  have h1 : ∫ t in (-S)..x, v' t = v x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hii _ _), hvL, sub_zero]
  have h2 : ∫ t in x..S, v' t = -v x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hii _ _), hvR, zero_sub]
  have hxabs : |x| ≤ S := by linarith
  have hxlt : -S ≤ x := (abs_le.mp hxabs).1
  have hxlt' : x ≤ S := (abs_le.mp hxabs).2
  have hb1 : |v x| ≤ ∫ t in (-S)..x, |v' t| := by
    rw [← h1]
    exact intervalIntegral.abs_integral_le_integral_abs hxlt
  have hb2 : |v x| ≤ ∫ t in x..S, |v' t| := by
    have : |(-v x)| ≤ ∫ t in x..S, |v' t| := by
      rw [← h2]
      exact intervalIntegral.abs_integral_le_integral_abs hxlt'
    simpa using this
  have hsum : (∫ t in (-S)..x, |v' t|) + (∫ t in x..S, |v' t|) = ∫ t in (-S)..S, |v' t| :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hv'.abs).intervalIntegrable _ _) ((hv'.abs).intervalIntegrable _ _)
  have hfinal : (∫ t in (-S)..S, |v' t|) ≤ ∫ t, |v' t| := by
    rw [intervalIntegral.integral_of_le (by linarith : (-S : ℝ) ≤ S)]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => abs_nonneg _)
  linarith

/-- **Gagliardo–Nirenberg interpolation inequality** (one-dimensional base case).

For a continuously differentiable, compactly supported function `u : ℝ → ℝ` with derivative `u'`,
the pointwise square of `u` is controlled by the product of the `L²` norms of `u` and `u'`:
`u x ^ 2 ≤ ‖u‖₂ * ‖u'‖₂`.  Equivalently `‖u‖_∞ ≤ ‖u‖₂^(1/2) * ‖u'‖₂^(1/2)`, the interpolation
between `L²` and `Ẇ^{1,2}` with exponent `1/2`. -/
