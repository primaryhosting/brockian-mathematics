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

private theorem Sform_nonneg (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (X : Matrix n n ℂ) : 0 ≤ Sform ρ σ t X := by
  have h1 : 0 ≤ (Matrix.trace (Xᴴ * σ * X)).re := by
    have := (hσ.conjTranspose_mul_mul_same X).trace_nonneg
    simpa using (Complex.le_def.mp this).1
  have h2 : 0 ≤ (Matrix.trace (Xᴴ * X * ρ)).re :=
    trace_mul_re_nonneg (Matrix.posSemidef_conjTranspose_mul_self X) hρ
  have := mul_nonneg ht h2
  simp only [Sform]
  linarith

section NoDecEq

omit [DecidableEq n]

/-- The Sylvester operator. -/
private noncomputable def Lmap (ρ σ : Matrix n n ℂ) (t : ℝ) (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  σ * Y + (t : ℂ) • (Y * ρ)

