import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace

/-- The Fourier transform of a Schwartz function on `ℝ`, written out as an explicit
oscillatory integral with the physics normalisation `e^{-2πi x w}`. -/
theorem fourier_schwartz_apply (f : 𝓢(ℝ, ℂ)) (w : ℝ) :
    (𝓕 f) w = ∫ x : ℝ, Complex.exp ((-2 * π * x * w : ℝ) * Complex.I) * f x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp [smul_eq_mul]

/-- **Parseval / Plancherel theorem for the Fourier transform.**

For a Schwartz function `f : ℝ → ℂ` (a wave function in the physics setting), the Fourier
transform, written explicitly with the kernel `e^{-2πi x w}`, preserves the `L²` norm:
the total probability computed in position space equals the one computed in momentum space. -/
theorem parseval_fourier (f : 𝓢(ℝ, ℂ)) :
    ∫ w : ℝ, ‖∫ x : ℝ, Complex.exp ((-2 * π * x * w : ℝ) * Complex.I) * f x‖ ^ 2
      = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have h : ∀ w : ℝ, (∫ x : ℝ, Complex.exp ((-2 * π * x * w : ℝ) * Complex.I) * f x)
      = (𝓕 f) w := fun w => (fourier_schwartz_apply f w).symm
  simp_rw [h]
  exact SchwartzMap.integral_norm_sq_fourier f

/-- Polarised form of Parseval's theorem: the Fourier transform preserves the `L²`
inner product of Schwartz functions. -/
theorem parseval_fourier_inner (f g : 𝓢(ℝ, ℂ)) :
    ∫ w : ℝ, ⟪(𝓕 f) w, (𝓕 g) w⟫ = ∫ x : ℝ, ⟪f x, g x⟫ :=
  SchwartzMap.integral_inner_fourier_fourier f g

/-- The Fourier transform on `L²(ℝ, ℂ)` is a linear isometry equivalence; in particular
it preserves norms (Plancherel's theorem for genuine `L²` functions). -/
theorem parseval_fourier_L2 (f : Lp (α := ℝ) ℂ 2) : ‖(𝓕 f)‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- The `L²` Fourier transform preserves inner products. -/
theorem parseval_fourier_L2_inner (f g : Lp (α := ℝ) ℂ 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  MeasureTheory.Lp.inner_fourier_eq f g

end QPhys

