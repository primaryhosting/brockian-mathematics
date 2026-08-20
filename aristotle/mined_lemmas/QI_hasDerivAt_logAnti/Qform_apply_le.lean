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

theorem Qform_apply_le (Φ : Channel n m ι) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (B : Matrix m m ℂ) :
    Qform (Φ.apply ρ) (Φ.apply σ) t B ≤ Qform ρ σ t (Φ.adjoint B) := by
  have hlin : (Matrix.trace (Φ.apply ρ * B)).re = (Matrix.trace (ρ * Φ.adjoint B)).re := by
    rw [Φ.trace_apply_mul]
  have h2 : (Matrix.trace ((Φ.adjoint B)ᴴ * σ * Φ.adjoint B)).re
      ≤ (Matrix.trace (Bᴴ * Φ.apply σ * B)).re := by
    have e1 : Matrix.trace ((Φ.adjoint B)ᴴ * σ * Φ.adjoint B)
        = Matrix.trace ((Φ.adjoint B * (Φ.adjoint B)ᴴ) * σ) := by
      rw [Matrix.trace_mul_comm ((Φ.adjoint B)ᴴ * σ) (Φ.adjoint B), ← Matrix.mul_assoc]
    have e2 : Matrix.trace (Bᴴ * Φ.apply σ * B) = Matrix.trace (Φ.adjoint (B * Bᴴ) * σ) := by
      rw [Matrix.trace_mul_comm (Bᴴ * Φ.apply σ) B, ← Matrix.mul_assoc,
        Matrix.trace_mul_comm (B * Bᴴ) (Φ.apply σ), Φ.trace_apply_mul σ (B * Bᴴ),
        Matrix.trace_mul_comm]
    rw [e1, e2]
    exact trace_mul_re_mono (Φ.kadison_schwarz' B) hσ
  have h3 : (Matrix.trace ((Φ.adjoint B)ᴴ * Φ.adjoint B * ρ)).re
      ≤ (Matrix.trace (Bᴴ * B * Φ.apply ρ)).re := by
    have e2 : Matrix.trace (Bᴴ * B * Φ.apply ρ) = Matrix.trace (Φ.adjoint (Bᴴ * B) * ρ) := by
      rw [Matrix.trace_mul_comm (Bᴴ * B) (Φ.apply ρ), Φ.trace_apply_mul ρ (Bᴴ * B),
        Matrix.trace_mul_comm]
    rw [e2]
    exact trace_mul_re_mono (Φ.kadison_schwarz B) hρ
  have h3' : t * (Matrix.trace ((Φ.adjoint B)ᴴ * Φ.adjoint B * ρ)).re
      ≤ t * (Matrix.trace (Bᴴ * B * Φ.apply ρ)).re := mul_le_mul_of_nonneg_left h3 ht
  simp only [Qform]
  rw [hlin]
  linarith

/-- **Monotonicity of the resolvent form under quantum channels.** -/
