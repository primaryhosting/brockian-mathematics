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

theorem momentumWave_eq_fourier (psi : ℝ → ℂ) (p : ℝ) :
    momentumWave psi p = 𝓕 psi p := by
  rw [Real.fourier_eq' psi p]
  simp only [momentumWave, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  congr 1 with x
  congr 2
  push_cast
  ring

/-- **Parseval/Plancherel theorem** for the Fourier transform: the Fourier transform preserves
the `L²` norm.  For a Schwartz-class wave function `psi` on the line, the total probability
computed in momentum space equals the total probability computed in position space:
`∫ ‖(𝓕 psi)(p)‖² dp = ∫ ‖psi x‖² dx`. -/
