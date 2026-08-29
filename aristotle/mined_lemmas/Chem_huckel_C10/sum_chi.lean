import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem sum_chi (m : ZMod 10) : ∑ k : ZMod 10, chi (k * m) = if m = 0 then 10 else 0 := by
  simp only [chi_mul_pow]
  rw [sum_zmod_range (fun n => (chi m) ^ n)]
  by_cases hm : m = 0
  · subst hm
    simp [chi]
  · have hz : chi m ≠ 1 :=
      om_primitive.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero m).mpr hm) (ZMod.val_lt m)
    have h10 : (chi m) ^ 10 = 1 := by
      rw [chi, ← pow_mul, mul_comm, pow_mul, om_pow_ten, one_pow]
    rw [geom_sum_eq hz, h10]
    simp [hm]

