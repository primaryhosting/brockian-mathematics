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

theorem parseval_fourier_L2 (f : Lp (α := ℝ) ℂ 2) : ‖(𝓕 f : Lp (α := ℝ) ℂ 2)‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- The `L²` Fourier transform preserves inner products (polarized Plancherel). -/
