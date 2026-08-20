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

import RequestProject.QI.Spectral

/-!
# An integral formula for the relative entropy

The elementary scalar identity

`∫_0^∞ (a²/(b + t a) - a/(1 + t)) dt = a (log a - log b)`  (`QI.integral_scalar`)

for `a, b > 0`, combined with the spectral formulas of `RequestProject.QI.Spectral`, gives the
integral representation

`relEntropy ρ σ = ∫_{t ∈ (0, ∞)} (Rval ρ σ t - (tr ρ).re / (1 + t)) dt`

(`QI.relEntropy_eq_integral`) for positive definite `ρ`, `σ`.  Since `Rval` is monotone under
quantum channels, this immediately yields the data-processing inequality.
-/

namespace QI

open Real MeasureTheory Filter Set Matrix
open scoped Topology ComplexOrder BigOperators MatrixOrder

/-! ### The scalar integral -/

/-- The antiderivative of `t ↦ a²/(b + t a) - a/(1 + t)`. -/

theorem tendsto_logAnti {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (logAnti a b) atTop (𝓝 (a * Real.log a)) := by
  have hfrac : Tendsto (fun t : ℝ => (b + t * a) / (1 + t)) atTop (𝓝 a) := by
    have h1 : Tendsto (fun t : ℝ => (b - a) / (1 + t)) atTop (𝓝 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_left _ 1 tendsto_id
    have h2 := (tendsto_const_nhds (x := a) (f := atTop (α := ℝ))).add h1
    rw [add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h2' : (0 : ℝ) < 1 + t := by positivity
    field_simp
    ring
  have hlog := (Real.continuousAt_log ha.ne').tendsto.comp hfrac
  refine (hlog.const_mul a).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have h1 : (0 : ℝ) < b + t * a := by positivity
  have h2 : (0 : ℝ) < 1 + t := by positivity
  simp [logAnti, Function.comp, Real.log_div h1.ne' h2.ne']

/-- The scalar integrand, in factored form; note that its sign does not depend on `t`. -/
