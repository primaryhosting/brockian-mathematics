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

lemma zeta_pow_sub (n : ℕ) [NeZero n] (a b c : ℕ) :
    zeta n ^ (a * c) * (zeta n)⁻¹ ^ (b * c) = (zeta n ^ ((a : ℤ) - b)) ^ c := by
  rw [← zpow_natCast (zeta n ^ ((a : ℤ) - b)) c, ← _root_.zpow_mul, sub_mul,
    zpow_sub₀ (zeta_ne_zero n), inv_pow, ← zpow_natCast (zeta n) (a * c),
    ← zpow_natCast (zeta n) (b * c), div_eq_mul_inv]
  push_cast
  ring

/-- The `n`-point quantum Fourier transform matrix: `(1/√n) · ω^(j·k)` with `ω = exp (2πi/n)`. -/
