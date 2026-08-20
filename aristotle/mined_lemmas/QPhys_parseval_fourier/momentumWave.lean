/-
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

open MeasureTheory Complex
open scoped FourierTransform

/-- The momentum-space wave function associated to a position-space wave function `psi`,
i.e. the (unitary, angular-frequency-free) Fourier transform
`(𝓕 psi)(p) = ∫ e^{-2πi p x} psi x dx`. -/

noncomputable def momentumWave (psi : ℝ → ℂ) (p : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(2 * Real.pi * p * x) * Complex.I) * psi x

/-- `momentumWave` is exactly Mathlib's Fourier transform on `ℝ`. -/
