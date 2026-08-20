import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma dvd_add_sub_mod {p s j : ℕ} (hp : 0 < p) (hj : j < p) :
    (p ∣ s + (p - j) % p) ↔ s % p = j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [Nat.dvd_iff_mod_eq_zero]
  · have hr : (p - j) % p = p - j := Nat.mod_eq_of_lt (by omega)
    rw [hr]
    set b := s % p with hb
    have hbp : b < p := Nat.mod_lt _ hp
    have key : (s + (p - j)) % p = (b + p - j) % p := by
      conv_lhs => rw [Nat.add_mod]
      rw [← hb, Nat.mod_eq_of_lt (show p - j < p by omega)]
      congr 1
      omega
    rw [Nat.dvd_iff_mod_eq_zero, key]
    rcases lt_trichotomy b j with h | h | h
    · rw [Nat.mod_eq_of_lt (by omega)]
      constructor <;> intro <;> omega
    · rw [h, show j + p - j = p by omega, Nat.mod_self]
      simp
    · rw [show b + p - j = p + (b - j) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)]
      constructor <;> intro <;> omega

/-- The heart of the Razborov–Smolensky argument, over an abstract field `F` of characteristic
`q` containing a nontrivial `p`-th root of unity. -/
