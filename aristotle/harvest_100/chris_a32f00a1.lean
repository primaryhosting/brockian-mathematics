import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap

namespace QPhys

/-- **Plancherel/Parseval theorem**: the Fourier transform is an `L²` isometry.

For a finite-dimensional real inner product space `E` (e.g. `ℝ` or `ℝ³`, the configuration
space of a quantum system) and a complex Hilbert space `F` of values, the Fourier transform
`𝓕` acting on `L²(E, F)` preserves both the norm and the inner product:
the position-space wavefunction and the momentum-space wavefunction have the same `L²` norm,
and inner products (hence transition amplitudes) are preserved.

This is a direct consequence of the fact that Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ`
is a linear isometry equivalence; the two components are
`MeasureTheory.Lp.norm_fourier_eq` and `MeasureTheory.Lp.inner_fourier_eq`. -/
theorem parseval_fourier
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f g : Lp (α := E) F 2) :
    ‖𝓕 f‖ = ‖f‖ ∧ ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  ⟨Lp.norm_fourier_eq f, Lp.inner_fourier_eq f g⟩

/-- The Fourier transform on `L²` is a linear isometry equivalence: the abstract form of
Plancherel's theorem, from which `QPhys.parseval_fourier` follows. -/
theorem fourier_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    Isometry (Lp.fourierTransformₗᵢ E F) :=
  (Lp.fourierTransformₗᵢ E F).isometry

/-- Parseval's identity in integral form for a wavefunction on the line: the total probability
computed from the position-space wavefunction equals the one computed from its Fourier
transform. Stated for Schwartz functions, where all integrals converge absolutely. -/
theorem parseval_fourier_integral_norm_sq (f : 𝓢(ℝ, ℂ)) :
    ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 :=
  SchwartzMap.integral_norm_sq_fourier f

/-- Parseval's identity in integral form for inner products of two Schwartz wavefunctions
on the line. -/
theorem parseval_fourier_integral_inner (f g : 𝓢(ℝ, ℂ)) :
    ∫ ξ : ℝ, ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫ x : ℝ, ⟪f x, g x⟫ :=
  SchwartzMap.integral_inner_fourier_fourier f g

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

