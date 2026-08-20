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

theorem integrableOn_scalar {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => a ^ 2 / (b + t * a) - a / (1 + t)) (Ioi 0) := by
  rcases le_total b a with hab | hab
  · refine integrableOn_Ioi_deriv_of_nonneg' (g := logAnti a b)
      (fun x hx => hasDerivAt_logAnti ha hb hx) (fun x hx => ?_) (tendsto_logAnti ha hb)
    have hx' : (0 : ℝ) < x := hx
    rw [scalar_integrand_eq ha hb hx'.le]
    have h1 : (0 : ℝ) < b + x * a := by positivity
    have h2 : (0 : ℝ) < 1 + x := by positivity
    have h3 : 0 ≤ a * (a - b) := by nlinarith
    positivity
  · refine integrableOn_Ioi_deriv_of_nonpos' (g := logAnti a b)
      (fun x hx => hasDerivAt_logAnti ha hb hx) (fun x hx => ?_) (tendsto_logAnti ha hb)
    have hx' : (0 : ℝ) < x := hx
    rw [scalar_integrand_eq ha hb hx'.le]
    have h1 : (0 : ℝ) < b + x * a := by positivity
    have h2 : (0 : ℝ) < 1 + x := by positivity
    have h3 : a * (a - b) ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg h3 (by positivity)

/-- The scalar integral underlying the integral representation of the relative entropy. -/
