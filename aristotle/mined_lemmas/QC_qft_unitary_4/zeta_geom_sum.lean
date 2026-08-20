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

lemma zeta_geom_sum (n : ℕ) [NeZero n] (d : ℤ) (hd : ¬ ((n : ℤ) ∣ d)) :
    ∑ k ∈ Finset.range n, (zeta n ^ d) ^ (k : ℕ) = 0 := by
  have hne : zeta n ^ d ≠ 1 := fun h =>
    hd (((zeta_isPrimitiveRoot n).zpow_eq_one_iff_dvd d).mp h)
  have hpow : (zeta n ^ d) ^ n = 1 := by
    rw [← zpow_natCast (zeta n ^ d) n, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, zeta_pow_self n, _root_.one_zpow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- Splitting a power of `ζₙ` indexed by a difference of exponents. -/
