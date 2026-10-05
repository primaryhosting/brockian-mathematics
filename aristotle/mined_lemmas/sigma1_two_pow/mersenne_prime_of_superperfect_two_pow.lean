import Mathlib


theorem mersenne_prime_of_superperfect_two_pow {k : ℕ}
    (h : Superperfect (2 ^ k)) : Nat.Prime (2 ^ (k + 1) - 1) := by
  obtain ⟨-, h⟩ := h
  rw [sigma1_two_pow k] at h
  apply prime_of_sigma1_eq_succ
  have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [h, pow_succ 2 k]
  omega

