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

theorem fourier_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    Isometry (Lp.fourierTransformₗᵢ E F) :=
  (Lp.fourierTransformₗᵢ E F).isometry

/-- Parseval's identity in integral form for a wavefunction on the line: the total probability
computed from the position-space wavefunction equals the one computed from its Fourier
transform. Stated for Schwartz functions, where all integrals converge absolutely. -/
