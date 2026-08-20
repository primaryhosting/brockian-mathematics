import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma choose_inequality_succ {N k r : ℕ} (hkN : k ≤ N) (hrk : r ≤ k)
    (h : N ^ r < Nat.choose N k) :
    (N + 1) ^ r < Nat.choose (N + 1) k := by
  have hleft_le : (N + 1) ^ r * (N + 1 - k) ≤ N ^ r * (N + 1) := by
    calc
      (N + 1) ^ r * (N + 1 - k)
          ≤ (N + 1) ^ r * (N + 1 - r) :=
            Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hrk (N + 1))
      _ ≤ N ^ r * (N + 1) := succ_pow_mul_sub_le_pow_mul_succ (N := N) (r := r) (by omega)
  have hright_lt : N ^ r * (N + 1) < Nat.choose N k * (N + 1) :=
    Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos N)
  have hprod_lt :
      (N + 1) ^ r * (N + 1 - k) < Nat.choose (N + 1) k * (N + 1 - k) := by
    calc
      (N + 1) ^ r * (N + 1 - k) ≤ N ^ r * (N + 1) := hleft_le
      _ < Nat.choose N k * (N + 1) := hright_lt
      _ = Nat.choose (N + 1) k * (N + 1 - k) := Nat.choose_mul_succ_eq N k
  exact Nat.lt_of_mul_lt_mul_right hprod_lt

