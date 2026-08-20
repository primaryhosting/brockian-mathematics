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

private theorem trace_Lmap_symm (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (X Y : Matrix n n ℂ) :
    (starRingEnd ℂ) (Matrix.trace (Xᴴ * Lmap ρ σ t Y)) = Matrix.trace (Yᴴ * Lmap ρ σ t X) := by
  rw [← trace_Lmap, ← trace_Lmap, map_add, map_mul]
  congr 1
  · rw [show (starRingEnd ℂ) (Matrix.trace (Xᴴ * σ * Y)) = Matrix.trace ((Xᴴ * σ * Y)ᴴ) from
      (Matrix.trace_conjTranspose _).symm]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hσ.eq,
      Matrix.mul_assoc]
  · rw [show (starRingEnd ℂ) (Matrix.trace (Xᴴ * Y * ρ)) = Matrix.trace ((Xᴴ * Y * ρ)ᴴ) from
      (Matrix.trace_conjTranspose _).symm]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hρ.eq]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    simp [Complex.conj_ofReal]

/-- For hermitian `ρ`, `tr(Xᴴ ρ)` is the complex conjugate of `tr(ρ X)`. -/
