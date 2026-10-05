/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial

namespace QPhys

/-! ## Hermite polynomials over `ℝ`

We reuse Mathlib's (probabilists') Hermite polynomials `Polynomial.hermite : ℕ → ℤ[X]`
(`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`), pushed forward to `ℝ[X]`.
-/

/-- The `n`-th (probabilists') Hermite polynomial, with real coefficients. -/

lemma oscWave_ne_zero {hbar m omega : ℝ} (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < omega) (n : ℕ) :
    oscWave hbar m omega n ≠ 0 := by
  obtain ⟨y, hy⟩ := psi_ne_zero n
  intro hzero
  have hc := scale_pos hh hm ho
  have : oscWave hbar m omega n (y / scale hbar m omega) = 0 := by rw [hzero]; rfl
  rw [oscWave, mul_div_cancel₀ _ (ne_of_gt hc)] at this
  exact hy this

/-- Each `ψₙ` (rescaled) is an eigenfunction with energy `ℏω(n + 1/2)`. -/
