/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QPhys

open MeasureTheory FourierTransform ComplexInnerProductSpace

noncomputable section

/-- The `L²` inner product of a wave function with itself is the integral of its squared
modulus (as a complex number). -/

theorem inner_self_eq_integral_norm_sq (f : Lp (α := ℝ) ℂ 2) :
    (inner ℂ f f) = ((∫ x, ‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ a : ℝ,
      (inner ℂ ((f : ℝ → ℂ) a) ((f : ℝ → ℂ) a)) = ((‖(f : ℝ → ℂ) a‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    simp [inner_self_eq_norm_sq_to_K]
  rw [MeasureTheory.L2.inner_def]
  simp_rw [h]
  exact integral_complex_ofReal

/--
**Parseval/Plancherel theorem for the Fourier transform.**

The Fourier transform `𝓕` on `L²(ℝ, ℂ)` (the state space of a one-dimensional quantum
particle) is an isometry: it preserves the inner product, the norm, and hence the total
probability `∫ ‖ψ x‖ ^ 2`.

The heart of the argument is Mathlib's `MeasureTheory.Lp.inner_fourier_eq` /
`MeasureTheory.Lp.norm_fourier_eq`, which express that the `L²` Fourier transform is
built from the linear isometry equivalence `MeasureTheory.Lp.fourierTransformₗᵢ`.
-/
