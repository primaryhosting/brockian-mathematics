import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma exists_params (p q d c : ℕ) (hp : 2 ≤ p) (hd : 1 ≤ d) (hc : 1 ≤ c) :
    ∃ t l m : ℕ, 1 ≤ l ∧ m = 2 ^ t ∧
      (∀ k : ℕ, k ≤ c * (2 * m + 1 + p + 1) ^ c → 8 * p * k * 2 ^ p ≤ 2 ^ l) ∧
      9 * (((q - 1) * l) ^ d) ^ 2 ≤ m := by
  set A := 8 * p * 2 ^ p * c with hA
  set Bc := (q - 1) * (A + 4 * c) with hBc
  obtain ⟨t, ht0, htbig⟩ := exists_large_pow_le (9 * Bc ^ (2 * d)) (2 * d) (p + 4) (by omega)
  have hct : 1 ≤ c * (t + 3) := by
    have : 1 * 1 ≤ c * (t + 3) := Nat.mul_le_mul hc (by omega)
    omega
  refine ⟨t, A + c * (t + 3), 2 ^ t, by omega, rfl, ?_, ?_⟩
  · intro k hk
    have hNb : 2 * 2 ^ t + 1 + p + 1 ≤ 2 ^ (t + 2) := by
      have h1 : t + 1 < 2 ^ (t + 1) := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ (t + 2) = 2 ^ (t + 1) + 2 ^ (t + 1) := by ring
      have h3 : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
      omega
    have hkb : k ≤ c * 2 ^ (c * (t + 2)) := by
      refine le_trans hk ?_
      have h2 : (2 * 2 ^ t + 1 + p + 1) ^ c ≤ (2 ^ (t + 2)) ^ c := Nat.pow_le_pow_left hNb c
      calc c * (2 * 2 ^ t + 1 + p + 1) ^ c ≤ c * (2 ^ (t + 2)) ^ c := Nat.mul_le_mul_left _ h2
        _ = c * 2 ^ (c * (t + 2)) := by rw [← pow_mul, mul_comm (t + 2) c]
    calc 8 * p * k * 2 ^ p ≤ 8 * p * (c * 2 ^ (c * (t + 2))) * 2 ^ p :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hkb)
      _ = A * 2 ^ (c * (t + 2)) := by rw [hA]; ring
      _ ≤ 2 ^ A * 2 ^ (c * (t + 2)) := Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ (A + c * (t + 2)) := by rw [← pow_add]
      _ ≤ 2 ^ (A + c * (t + 3)) := by
          refine Nat.pow_le_pow_right (by omega) ?_
          have : c * (t + 2) ≤ c * (t + 3) := Nat.mul_le_mul_left _ (by omega)
          omega
  · have h1 : (q - 1) * (A + c * (t + 3)) ≤ Bc * t := by
      have h2 : A + c * (t + 3) ≤ (A + 4 * c) * t := by nlinarith [ht0]
      calc (q - 1) * (A + c * (t + 3)) ≤ (q - 1) * ((A + 4 * c) * t) :=
            Nat.mul_le_mul_left _ h2
        _ = Bc * t := by rw [hBc]; ring
    have h2 : ((q - 1) * (A + c * (t + 3))) ^ d ≤ Bc ^ d * t ^ d := by
      calc ((q - 1) * (A + c * (t + 3))) ^ d ≤ (Bc * t) ^ d := Nat.pow_le_pow_left h1 d
        _ = Bc ^ d * t ^ d := by rw [mul_pow]
    calc 9 * (((q - 1) * (A + c * (t + 3))) ^ d) ^ 2 ≤ 9 * (Bc ^ d * t ^ d) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 2)
      _ = 9 * Bc ^ (2 * d) * t ^ (2 * d) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm d 2, mul_assoc]
      _ ≤ 2 ^ t := htbig

/-- For distinct primes `p` and `q` there is a finite field of characteristic `q` containing a
`p`-th root of unity different from `1`. -/
