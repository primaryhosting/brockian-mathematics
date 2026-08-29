import Mathlib
/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi/N)` used to build the QFT matrix. -/

lemma sum_qftOmega_pow_eq_zero {N d : ℕ} (hd : d ≠ 0) (hdN : d < N) :
    ∑ m ∈ Finset.range N, (qftOmega N ^ d) ^ m = 0 := by
  have hN : N ≠ 0 := by omega
  have hprim := isPrimitiveRoot_qftOmega hN
  have hne : qftOmega N ^ d ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hd hdN
  have hpow : (qftOmega N ^ d) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

