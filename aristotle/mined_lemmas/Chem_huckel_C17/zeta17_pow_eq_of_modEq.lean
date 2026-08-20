import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma zeta17_pow_eq_of_modEq {a b : ℕ} (h : a % 17 = b % 17) :
    zeta17 ^ a = zeta17 ^ b := by
  have h17 : zeta17 ^ (17 : ℕ) = 1 := isPrimitiveRoot_zeta17.pow_eq_one
  have key : ∀ n : ℕ, zeta17 ^ n = zeta17 ^ (n % 17) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 17]
    rw [pow_add, pow_mul, h17, one_pow, one_mul]
  rw [key a, key b, h]

