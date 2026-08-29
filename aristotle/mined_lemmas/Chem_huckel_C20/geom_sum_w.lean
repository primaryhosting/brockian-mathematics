import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma geom_sum_w (t : ZMod 20) :
    ∑ m ∈ range 20, w ^ (m * t.val) = if t = 0 then 20 else 0 := by
  by_cases ht : t = 0
  · subst ht
    simp
  · rw [if_neg ht]
    have hz : w ^ t.val ≠ 1 := by
      intro hz
      have hdvd : (20 : ℕ) ∣ t.val := (w_isPrimitiveRoot.pow_eq_one_iff_dvd _).1 hz
      have hlt : t.val < 20 := ZMod.val_lt t
      have hne : t.val ≠ 0 := by
        intro h0
        exact ht ((ZMod.val_eq_zero t).1 h0)
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
      omega
    have : ∑ m ∈ range 20, w ^ (m * t.val) = ∑ m ∈ range 20, (w ^ t.val) ^ m := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← pow_mul, Nat.mul_comm]
    rw [this, geom_sum_eq hz, ← pow_mul, Nat.mul_comm, pow_mul, w_pow_20, one_pow, sub_self,
      zero_div]

/-- If all `20` discrete Fourier coefficients of `x` vanish, then `x = 0`. -/
