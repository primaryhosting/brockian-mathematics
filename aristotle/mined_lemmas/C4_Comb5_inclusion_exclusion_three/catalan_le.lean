import Mathlib
open Finset
namespace C4.Comb5


theorem catalan_le (n : ℕ) : catalan n ≤ 4^n := by
  have h : (n + 1) * catalan n = n.centralBinom := succ_mul_catalan_eq_centralBinom n
  have hb : n.centralBinom ≤ 4 ^ n := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    calc (2 * n).choose n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  calc catalan n ≤ (n + 1) * catalan n := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    _ = n.centralBinom := h
    _ ≤ 4 ^ n := hb

end C4.Comb5

