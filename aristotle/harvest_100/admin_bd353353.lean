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

open MeasureTheory SchwartzMap Real
open scoped FourierTransform ComplexInnerProductSpace

namespace QPhys

/-- **Plancherel/Parseval theorem**: the Fourier transform is an isometry of `L²`.

Here `𝓕` denotes the Fourier transform on `L²(ℝ, ℂ)` (with respect to Lebesgue measure),
and the statement says that it preserves the `L²` norm. -/
theorem parseval_fourier (f : Lp (α := ℝ) ℂ 2) : ‖𝓕 f‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- Polarized form of Parseval's identity: the Fourier transform on `L²(ℝ, ℂ)` preserves
the inner product. -/
theorem parseval_fourier_inner (f g : Lp (α := ℝ) ℂ 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  MeasureTheory.Lp.inner_fourier_eq f g

/-- Parseval's identity in concrete integral form, for Schwartz functions on `ℝ`:
`∫ ‖f x‖² dx = ∫ ‖(𝓕 f) ξ‖² dξ`. -/
theorem parseval_fourier_schwartz (f : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, ‖f x‖ ^ 2 = ∫ xi : ℝ, ‖𝓕 (⇑f) xi‖ ^ 2 :=
  (SchwartzMap.integral_norm_sq_fourier f).symm

/-- Parseval's identity for Schwartz functions with the Fourier transform written out
explicitly as `(𝓕 f)(ξ) = ∫ e^{-2πi x ξ} f(x) dx`. -/
theorem parseval_fourier_explicit (f : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, ‖f x‖ ^ 2 =
      ∫ xi : ℝ, ‖∫ x : ℝ, Complex.exp (-(2 * π * Complex.I * x * xi)) * f x‖ ^ 2 := by
  have key : ∀ xi : ℝ, 𝓕 (⇑f) xi
      = ∫ x : ℝ, Complex.exp (-(2 * π * Complex.I * x * xi)) * f x := by
    intro xi
    rw [Real.fourier_eq]
    congr 1 with x
    rw [Circle.smul_def, Real.fourierChar_apply, RCLike.inner_apply, conj_trivial]
    push_cast
    rw [smul_eq_mul]
    ring_nf
  simp_rw [← key]
  exact parseval_fourier_schwartz f

end QPhys

