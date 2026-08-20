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
