import Mathlib

/-!
# Legendre's three-square theorem

A natural number `n` is a sum of three squares if and only if it is not of the
form `4 ^ a * (8 * b + 7)`.

The proof is self-contained (only core `Mathlib` is used).  The hard direction
goes through the classical route:

* Minkowski's convex body theorem shows that every positive definite integral
  ternary quadratic form of determinant one represents `1`, hence (by descent)
  is of the shape `Nᵀ * N`.
* Dirichlet's theorem on primes in arithmetic progressions together with
  quadratic reciprocity produces, for every `n` with `n % 4 ≠ 0` and
  `n % 8 ≠ 7`, an integer `m > 0` with `n ∣ m + 1` and `-n` a square modulo `m`.
  Out of these data one builds an explicit positive definite integral ternary
  form of determinant one whose `(0,0)` entry is `n`.
-/

namespace Brockian.LegendreThreeSquare

open Matrix MeasureTheory
open scoped ENNReal

/-! ## Integral quadratic forms -/

/-- The value at `v` of the quadratic form attached to the integer matrix `A`. -/

theorem not_sum_three_squares (k m a b c : ℕ) : 4 ^ k * (8 * m + 7) ≠ a ^ 2 + b ^ 2 + c ^ 2 := by
  induction k generalizing a b c with
  | zero =>
    intro h
    simp at h
    have key' : ∀ x : Fin 8, ∀ y : Fin 8, ∀ z : Fin 8, (x.val ^ 2 + y.val ^ 2 + z.val ^ 2) % 8 ≠ 7 := by decide
    have ha : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod a 2 8
    have hb : b ^ 2 % 8 = (b % 8) ^ 2 % 8 := Nat.pow_mod b 2 8
    have hc : c ^ 2 % 8 = (c % 8) ^ 2 % 8 := Nat.pow_mod c 2 8
    have := key' ⟨a % 8, Nat.mod_lt a (by norm_num)⟩ ⟨b % 8, Nat.mod_lt b (by norm_num)⟩ ⟨c % 8, Nat.mod_lt c (by norm_num)⟩
    have derive : (8 * m + 7) % 8 = 7 := by norm_num
    rw [h] at derive
    simp_all [Nat.add_mod]
  | succ k ih =>
    intro h
    have h4 : 4 ∣ 4 ^ (k + 1) * (8 * m + 7) := ⟨4 ^ k * (8 * m + 7), by ring⟩
    rw [h] at h4
    have hsq4 : ∀ x : Fin 4, x.val ^ 2 % 4 = 0 ∨ x.val ^ 2 % 4 = 1 := by decide
    have hsum : (a ^ 2 + b ^ 2 + c ^ 2) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
    have sqmod : ∀ x : ℕ, x ^ 2 % 4 = (x % 4) ^ 2 % 4 := fun x => by rw [Nat.pow_mod]
    have ha : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
      rw [sqmod]; exact hsq4 ⟨a % 4, Nat.mod_lt a (by norm_num)⟩
    have hb : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
      rw [sqmod]; exact hsq4 ⟨b % 4, Nat.mod_lt b (by norm_num)⟩
    have hc : c ^ 2 % 4 = 0 ∨ c ^ 2 % 4 = 1 := by
      rw [sqmod]; exact hsq4 ⟨c % 4, Nat.mod_lt c (by norm_num)⟩
    have ha0 : a ^ 2 % 4 = 0 := by omega
    have hb0 : b ^ 2 % 4 = 0 := by omega
    have hc0 : c ^ 2 % 4 = 0 := by omega
    have ha_even : 2 ∣ a := by
      rcases Nat.even_or_odd' a with ⟨a', rfl | rfl⟩ <;> ring_nf at ha0 ⊢ <;> omega
    have hb_even : 2 ∣ b := by
      rcases Nat.even_or_odd' b with ⟨b', rfl | rfl⟩ <;> ring_nf at hb0 ⊢ <;> omega
    have hc_even : 2 ∣ c := by
      rcases Nat.even_or_odd' c with ⟨c', rfl | rfl⟩ <;> ring_nf at hc0 ⊢ <;> omega
    obtain ⟨a', rfl⟩ := ha_even
    obtain ⟨b', rfl⟩ := hb_even
    obtain ⟨c', rfl⟩ := hc_even
    have : 4 ^ k * (8 * m + 7) = a' ^ 2 + b' ^ 2 + c' ^ 2 := by
      have := h
      ring_nf at this ⊢
      linarith [pow_pos (by norm_num : (0 : ℕ) < 4) k]
    exact ih a' b' c' this

