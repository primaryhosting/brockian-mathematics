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
theorem parseval_fourier (psi : SchwartzMap ℝ ℂ) :
    ∫ p : ℝ, ‖momentumWave psi p‖ ^ 2 = ∫ x : ℝ, ‖psi x‖ ^ 2 := by
  simp only [momentumWave_eq_fourier]
  exact SchwartzMap.integral_norm_sq_fourier psi

/-- The polarized form of Parseval's identity: the Fourier transform preserves the `L²` inner
product of two Schwartz-class wave functions. -/
theorem parseval_fourier_inner (psi phi : SchwartzMap ℝ ℂ) :
    ∫ p : ℝ, (starRingEnd ℂ) (momentumWave psi p) * momentumWave phi p
      = ∫ x : ℝ, (starRingEnd ℂ) (psi x) * phi x := by
  simp only [momentumWave_eq_fourier]
  simpa [RCLike.inner_apply, mul_comm] using SchwartzMap.integral_inner_fourier_fourier psi phi

/-- The Fourier transform is an isometry of `L²(ℝ, ℂ)`: Plancherel's theorem in its
operator-theoretic form. -/
theorem parseval_fourier_L2 (f : Lp (α := ℝ) ℂ 2) : ‖𝓕 f‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

end QPhys

