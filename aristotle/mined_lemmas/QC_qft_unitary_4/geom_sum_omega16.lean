/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A primitive `16`-th root of unity, `exp (2πi/16)`. -/

lemma geom_sum_omega16 (i k : Fin 16) :
    ∑ j : Fin 16, (omega16 ^ i.val / omega16 ^ k.val) ^ j.val
      = if i = k then 16 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (omega16 ^ i.val / omega16 ^ k.val) ^ j) 16]
  by_cases h : i = k
  · subst h
    rw [div_self (pow_ne_zero _ omega16_ne_zero)]
    simp
  · have hne : omega16 ^ k.val ≠ 0 := pow_ne_zero _ omega16_ne_zero
    have hz1 : omega16 ^ i.val / omega16 ^ k.val ≠ 1 := by
      intro hzz
      exact h (Fin.ext (isPrimitiveRoot_omega16.pow_inj i.isLt k.isLt
        (div_eq_one_iff_eq hne |>.mp hzz)))
    have hz16 : (omega16 ^ i.val / omega16 ^ k.val) ^ 16 = 1 := by
      rw [div_pow, omega16_pow_pow_16, omega16_pow_pow_16, div_one]
    rw [geom_sum_eq hz1, hz16]
    simp [h]

/-- The 4-qubit quantum Fourier transform matrix is unitary. -/
