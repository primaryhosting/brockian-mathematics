import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma pow_le_pow_mul_choose (n k : ℕ) (hk : k ≤ n) :
    n ^ k ≤ k ^ k * Nat.choose n k := by
  refine Nat.le_induction (m := k)
    (P := fun N _ => N ^ k ≤ k ^ k * Nat.choose N k) ?_ ?_ n hk
  · simp
  · intro N hkN ih
    have hsub_pos : 0 < N + 1 - k := by omega
    refine Nat.le_of_mul_le_mul_right ?_ hsub_pos
    calc
      (N + 1) ^ k * (N + 1 - k) ≤ N ^ k * (N + 1) :=
        succ_pow_mul_sub_le_pow_mul_succ (N := N) (r := k) (by omega)
      _ ≤ (k ^ k * Nat.choose N k) * (N + 1) :=
        Nat.mul_le_mul_right _ ih
      _ = k ^ k * (Nat.choose N k * (N + 1)) := by ring
      _ = k ^ k * (Nat.choose (N + 1) k * (N + 1 - k)) := by
        rw [Nat.choose_mul_succ_eq]
      _ = (k ^ k * Nat.choose (N + 1) k) * (N + 1 - k) := by ring

