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

theorem hasDerivAt_logAnti {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (logAnti a b) (a ^ 2 / (b + t * a) - a / (1 + t)) t := by
  have hden : b + t * a ≠ 0 := by positivity
  have hden2 : (1 : ℝ) + t ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => b + s * a) a t := by
    simpa using ((hasDerivAt_id t).mul_const a).const_add b
  have h2 : HasDerivAt (fun s : ℝ => Real.log (b + s * a)) (a / (b + t * a)) t := h1.log hden
  have h3 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
    have h : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by simpa using (hasDerivAt_id t).const_add 1
    exact h.log hden2
  have h4 := (h2.sub h3).const_mul a
  have heq : a * (a / (b + t * a) - 1 / (1 + t)) = a ^ 2 / (b + t * a) - a / (1 + t) := by
    field_simp
  rwa [heq] at h4

