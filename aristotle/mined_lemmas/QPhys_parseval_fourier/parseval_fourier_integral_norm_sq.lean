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

theorem parseval_fourier_integral_norm_sq (f : 𝓢(ℝ, ℂ)) :
    ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 :=
  SchwartzMap.integral_norm_sq_fourier f

/-- Parseval's identity in integral form for inner products of two Schwartz wavefunctions
on the line. -/
