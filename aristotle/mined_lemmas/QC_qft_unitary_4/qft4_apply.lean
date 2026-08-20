/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The quantum Fourier transform is unitary

We define the `n`-point discrete/quantum Fourier transform matrix

`qftMatrix n = (1/√n) * (ω^(j*k))_{j,k}` with `ω = exp (2πi/n)`,

prove it is unitary for every `n ≠ 0`, and specialize to the 4-qubit case `n = 2^4 = 16`,
giving the target theorem `QC.qft_unitary_4`.
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma qft4_apply (j k : Fin 16) :
    qft4 j k = (1 / 4 : ℂ) * Complex.exp (2 * Real.pi * Complex.I / 16) ^ (j.val * k.val) := by
  have h : Real.sqrt (16 : ℕ) = 4 := by
    rw [show ((16 : ℕ) : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [qft4, qftMatrix, zeta, Matrix.of_apply, h]
  norm_num

/-- **The 4-qubit quantum Fourier transform matrix is unitary.** -/
