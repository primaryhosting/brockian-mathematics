import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Note: Lean 4 requires `import` statements to come first in a file, so the header
module docstring above is placed immediately after the single `import Mathlib` line.
-/

open scoped BigOperators
open scoped Real
open scoped FourierTransform
open scoped ComplexInnerProductSpace

open MeasureTheory SchwartzMap

noncomputable section

namespace QPhys

/-- The one-dimensional Fourier transform of a wave function, written with the explicit
oscillatory kernel `e^{-2πi x p}` used in physics:
`(𝓕 ψ)(p) = ∫ e^{-2 π i x p} ψ(x) dx`. -/
def fourier1D (psi : ℝ → ℂ) (p : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(2 * Real.pi * (x * p) * Complex.I)) * psi x

/-- On Schwartz functions, `QPhys.fourier1D` agrees with Mathlib's Fourier transform `𝓕`. -/
theorem fourier1D_eq (psi : 𝓢(ℝ, ℂ)) (p : ℝ) : fourier1D psi p = 𝓕 psi p := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  refine (integral_congr_ae (.of_forall fun v => ?_)).symm
  show ((Real.fourierChar (-(inner ℝ v p : ℝ)) : Circle) : ℂ) • psi v = _
  rw [show (inner ℝ v p : ℝ) = v * p by simp [mul_comm], Real.fourierChar_apply, smul_eq_mul]
  push_cast
  ring_nf

/-- **Parseval/Plancherel theorem for the Fourier transform.**

For a wave function `ψ` in Schwartz space on the line, the total probability is preserved by
the Fourier transform (passage from position space to momentum space):
`∫ |ψ̂(p)|² dp = ∫ |ψ(x)|² dx`, where `ψ̂(p) = ∫ e^{-2πi x p} ψ(x) dx`. -/
theorem parseval_fourier (psi : 𝓢(ℝ, ℂ)) :
    ∫ p : ℝ, ‖∫ x : ℝ, Complex.exp (-(2 * Real.pi * (x * p) * Complex.I)) * psi x‖ ^ 2
      = ∫ x : ℝ, ‖psi x‖ ^ 2 := by
  have h : ∀ p : ℝ,
      ‖∫ x : ℝ, Complex.exp (-(2 * Real.pi * (x * p) * Complex.I)) * psi x‖ ^ 2
        = ‖𝓕 psi p‖ ^ 2 := fun p => by rw [← fourier1D_eq psi p]; rfl
  simp_rw [h]
  exact SchwartzMap.integral_norm_sq_fourier psi

/-- Parseval's identity in sesquilinear (inner-product) form: the Fourier transform preserves
the `L²` inner product of Schwartz wave functions. -/
theorem parseval_fourier_inner (psi phi : 𝓢(ℝ, ℂ)) :
    ∫ p : ℝ, (starRingEnd ℂ) (fourier1D psi p) * fourier1D phi p
      = ∫ x : ℝ, (starRingEnd ℂ) (psi x) * phi x := by
  simp_rw [fourier1D_eq]
  have h := SchwartzMap.integral_inner_fourier_fourier psi phi
  simpa [RCLike.inner_apply, mul_comm] using h

/-- **Plancherel's theorem as an `L²` isometry.** The Fourier transform on `L²(ℝ, ℂ)` preserves
norms, i.e. it is an isometry of Hilbert spaces. -/
theorem parseval_fourier_L2 (f : Lp (α := ℝ) ℂ 2) : ‖(𝓕 f : Lp (α := ℝ) ℂ 2)‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- The `L²` Fourier transform preserves inner products (polarized Plancherel). -/
theorem parseval_fourier_L2_inner (f g : Lp (α := ℝ) ℂ 2) :
    ⟪(𝓕 f : Lp (α := ℝ) ℂ 2), (𝓕 g : Lp (α := ℝ) ℂ 2)⟫ = ⟪f, g⟫ :=
  MeasureTheory.Lp.inner_fourier_eq f g

end QPhys

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

