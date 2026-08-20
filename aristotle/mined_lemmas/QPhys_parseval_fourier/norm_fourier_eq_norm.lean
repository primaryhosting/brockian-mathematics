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

theorem norm_fourier_eq_norm (f : Lp (α := ℝ) ℂ 2) : ‖𝓕 f‖ = ‖f‖ :=
  Lp.norm_fourier_eq f

/-- Polarized form of Parseval's identity: the Fourier transform preserves inner products
(overlaps of quantum states). -/
