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

theorem fourier1D_eq (psi : 𝓢(ℝ, ℂ)) (p : ℝ) : fourier1D psi p = 𝓕 psi p := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  refine (integral_congr_ae (.of_forall fun v => ?_)).symm
  show ((Real.fourierChar (-(inner ℝ v p : ℝ)) : Circle) : ℂ) • psi v = _
  rw [show (inner ℝ v p : ℝ) = v * p by simp [mul_comm], Real.fourierChar_apply, smul_eq_mul]
  push_cast
  ring_nf

/-- **Parseval/Plancherel theorem for the Fourier transform.**

For a wave function `ψ` in Schwartz space on the line, the total probability is preserved by
the Fourier transform (passage from position space to momentum space):
`∫ |ψ̂(p)|² dp = ∫ |ψ(x)|² dx`, where `ψ̂(p) = ∫ e^{-2πi x p} ψ(x) dx`. -/
