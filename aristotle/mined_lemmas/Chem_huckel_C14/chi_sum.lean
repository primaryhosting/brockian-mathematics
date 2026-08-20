import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma chi_sum (m : Fin 14) : ∑ k : Fin 14, chi (k * m) = if m = 0 then 14 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [chi_zero]
  · have hstep : ∀ k : Fin 14, chi (k * m) = (chi m) ^ k.val := by
      intro k
      rw [mul_comm, chi_mul]
    rw [if_neg hm]
    calc ∑ k : Fin 14, chi (k * m) = ∑ k : Fin 14, (chi m) ^ (k : ℕ) :=
          Finset.sum_congr rfl fun k _ => hstep k
      _ = ∑ t ∈ Finset.range 14, (chi m) ^ t := (Finset.sum_range _).symm
      _ = 0 := by rw [geom_sum_eq (chi_ne_one hm), chi_pow_14, sub_self, zero_div]

