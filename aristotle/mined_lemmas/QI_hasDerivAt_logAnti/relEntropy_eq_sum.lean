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

theorem relEntropy_eq_sum (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy ρ σ = ∑ j, ∑ i, ‖eigOverlap hρ hσ i j‖ ^ 2 *
      (hρ.eigenvalues j * (Real.log (hρ.eigenvalues j) - Real.log (hσ.eigenvalues i))) := by
  have hsplit : relEntropy ρ σ
      = (Matrix.trace (ρ * mlog ρ)).re - (Matrix.trace (ρ * mlog σ)).re := by
    rw [relEntropy, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [hsplit, trace_mul_mlog_self hρ, trace_mul_mlog hρ hσ]
  simp only [Complex.ofReal_re]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : hρ.eigenvalues j * Real.log (hρ.eigenvalues j)
      = ∑ i, ‖eigOverlap hρ hσ i j‖ ^ 2 * (hρ.eigenvalues j * Real.log (hρ.eigenvalues j)) := by
    rw [← Finset.sum_mul, sum_normSq_eigOverlap hρ hσ j, one_mul]
  rw [h1, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The trace of `ρ` is the sum of its eigenvalues. -/
