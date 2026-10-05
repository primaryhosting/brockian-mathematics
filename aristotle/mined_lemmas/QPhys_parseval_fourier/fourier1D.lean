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
