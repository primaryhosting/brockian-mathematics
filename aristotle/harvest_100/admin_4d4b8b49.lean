/-
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory FourierTransform ComplexInnerProductSpace

namespace QPhys

/-- For an `L²` function `f : ℝ → ℂ` (a one–dimensional wavefunction), the integral of `‖f‖²`
is the square of its `L²` norm. -/
theorem integral_norm_sq_eq_norm_sq (f : Lp (α := ℝ) ℂ 2) :
    ∫ x : ℝ, ‖f x‖ ^ 2 = ‖f‖ ^ 2 := by
  have h : ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := norm_sq_eq_re_inner f
  rw [h, MeasureTheory.L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, integral_ofReal, RCLike.ofReal_re]

/-- **Parseval/Plancherel theorem.** The Fourier transform on `L²(ℝ, ℂ)` preserves the total
probability: the integral of the squared modulus of a wavefunction equals the integral of the
squared modulus of its Fourier transform (its momentum-space wavefunction).

This is a consequence of Mathlib's `MeasureTheory.Lp.norm_fourier_eq`, which states that the
Fourier transform `𝓕` on `L²` is norm preserving (it is defined via the linear isometry
equivalence `MeasureTheory.Lp.fourierTransformₗᵢ`). -/
theorem parseval_fourier (f : Lp (α := ℝ) ℂ 2) :
    ∫ p : ℝ, ‖(𝓕 f : Lp (α := ℝ) ℂ 2) p‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [integral_norm_sq_eq_norm_sq, integral_norm_sq_eq_norm_sq, Lp.norm_fourier_eq]

/-- The Fourier transform on `L²` is an isometry: it preserves the `L²` norm. -/
theorem norm_fourier_eq_norm (f : Lp (α := ℝ) ℂ 2) : ‖𝓕 f‖ = ‖f‖ :=
  Lp.norm_fourier_eq f

/-- Polarized form of Parseval's identity: the Fourier transform preserves inner products
(overlaps of quantum states). -/
theorem inner_fourier_eq_inner (f g : Lp (α := ℝ) ℂ 2) :
    ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  Lp.inner_fourier_eq f g

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

