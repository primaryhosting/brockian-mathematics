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

noncomputable def Rval (ρ σ : Matrix n n ℂ) (t : ℝ) : ℝ := ⨆ B : Matrix n n ℂ, Qform ρ σ t B

/-! ### The Sylvester equation and maximality -/

section Sylvester

variable {ρ σ B₀ : Matrix n n ℂ} {t : ℝ}

/-- The positive form associated with the Sylvester operator `X ↦ σ X + t X ρ`. -/
private noncomputable def Sform (ρ σ : Matrix n n ℂ) (t : ℝ) (X : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (Xᴴ * σ * X)).re + t * (Matrix.trace (Xᴴ * X * ρ)).re

