import Mathlib
/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `8`-th root of unity `ω = exp(2πi/8)` used by the 3-qubit QFT. -/

lemma qftOmega_sum (m : ℕ) :
    ∑ k : Fin 8, qftOmega ^ ((k : ℕ) * m) = if 8 ∣ m then 8 else 0 := by
  have hrw : ∀ k : Fin 8, qftOmega ^ ((k : ℕ) * m) = (qftOmega ^ m) ^ (k : ℕ) := by
    intro k; rw [← pow_mul, Nat.mul_comm]
  simp_rw [hrw]
  rw [Fin.sum_univ_eq_sum_range (fun i => (qftOmega ^ m) ^ i) 8]
  by_cases h : 8 ∣ m
  · have hm : qftOmega ^ m = 1 := (qftOmega_pow_eq_one_iff m).mpr h
    simp [hm, h]
  · have hm : qftOmega ^ m ≠ 1 := fun hc => h ((qftOmega_pow_eq_one_iff m).mp hc)
    rw [geom_sum_eq hm]
    have h8 : (qftOmega ^ m) ^ 8 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, qftOmega_pow_eight, one_pow]
    simp [h8, h]

