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

theorem trace_conj_diag (U V : Matrix n n ℂ) (d1 d2 : n → ℂ) :
    Matrix.trace (U * diagonal d1 * star U * (V * diagonal d2 * star V))
      = Matrix.trace (diagonal d1 * (star V * U)ᴴ * diagonal d2 * (star V * U)) := by
  have hH : (star V * U)ᴴ = star U * V := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  rw [hH]
  have h := Matrix.trace_mul_comm (V * diagonal d2 * star V * U) (diagonal d1 * star U)
  have h2 := Matrix.trace_mul_comm (U * diagonal d1 * star U) (V * diagonal d2 * star V)
  simp only [Matrix.mul_assoc] at h h2 ⊢
  rw [h2, h]

