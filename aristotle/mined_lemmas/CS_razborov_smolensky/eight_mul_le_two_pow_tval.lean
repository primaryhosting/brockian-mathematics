import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem eight_mul_le_two_pow_tval (p c m : ℕ) :
    8 * p * (2 * m + p + 2) ^ c ≤ 2 ^ (tval p c m) := by
  set L := Nat.log 2 (2 * m + p + 2) + 1 with hL
  have h1 : 2 * m + p + 2 < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : (2 * m + p + 2) ^ c ≤ (2 ^ L) ^ c := Nat.pow_le_pow_left (le_of_lt h1) c
  have h3 : p ≤ 2 ^ p := le_of_lt Nat.lt_two_pow_self
  have h4 : 2 ^ (tval p c m) = (2 ^ L) ^ c * 2 ^ p * 8 := by
    rw [tval, ← hL, pow_add, pow_add, ← pow_mul']
    norm_num
  rw [h4]
  calc 8 * p * (2 * m + p + 2) ^ c ≤ 8 * 2 ^ p * (2 ^ L) ^ c :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) h2
    _ = (2 ^ L) ^ c * 2 ^ p * 8 := by ring

/-- The core inequality: if `MOD p` is computed by depth `d`, size `(n+2)^c` circuits with
`MOD q` gates, then for every `m` the central binomial coefficient must be large. -/
