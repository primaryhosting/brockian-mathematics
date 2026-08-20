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

theorem data_processing (Φ : Channel n m ι) {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef)
    (hσ : σ.PosDef) (hΦσ : (Φ.apply σ).PosDef) :
    relEntropy (Φ.apply ρ) (Φ.apply σ) ≤ relEntropy ρ σ := by
  have hΦρ : (Φ.apply ρ).PosDef := Φ.apply_posDef_of_apply_posDef hρ hΦσ
  have hint₁ := integrableOn_relIntegrand hΦρ hΦσ
  have hint₂ := integrableOn_relIntegrand hρ hσ
  rw [Φ.trace_apply ρ] at hint₁
  rw [relEntropy_eq_integral hΦρ hΦσ, relEntropy_eq_integral hρ hσ, Φ.trace_apply ρ]
  refine setIntegral_mono_on hint₁ hint₂ measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  obtain ⟨B₀, hB₀, -⟩ := exists_sylvester hρ hσ ht'
  have := Rval_apply_le Φ hρ.posSemidef hσ.posSemidef ht' hB₀
  linarith

end QI

