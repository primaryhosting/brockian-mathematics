import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma exists_large_pow_le (K e t₀ : ℕ) (he : 1 ≤ e) : ∃ t, t₀ ≤ t ∧ K * t ^ e ≤ 2 ^ t := by
  set u := K + e + 4 + t₀ with hu
  refine ⟨e * u + K, ?_, ?_⟩
  · calc t₀ ≤ u := by omega
      _ ≤ e * u := Nat.le_mul_of_pos_left u he
      _ ≤ e * u + K := Nat.le_add_right _ _
  · have h1 : e * u + K ≤ (e + 1) * u := by
      have : K ≤ u := by omega
      nlinarith
    have h2 : (e + 1) * u ≤ 2 ^ u := by
      have h3 : (e + 1) * u ≤ u * u := Nat.mul_le_mul_right u (by omega)
      have h4 : u * u = u ^ 2 := by ring
      exact le_trans h3 (h4 ▸ sq_le_two_pow (by omega))
    have h5 : (e * u + K) ^ e ≤ 2 ^ (u * e) := by
      calc (e * u + K) ^ e ≤ ((e + 1) * u) ^ e := Nat.pow_le_pow_left h1 e
        _ ≤ (2 ^ u) ^ e := Nat.pow_le_pow_left h2 e
        _ = 2 ^ (u * e) := by rw [← pow_mul]
    have h6 : K ≤ 2 ^ K := Nat.le_of_lt Nat.lt_two_pow_self
    calc K * (e * u + K) ^ e ≤ 2 ^ K * 2 ^ (u * e) := Nat.mul_le_mul h6 h5
      _ = 2 ^ (e * u + K) := by rw [← pow_add]; ring_nf

/-- Choice of the parameters in the Razborov–Smolensky argument: a number of inputs
`n = 2m+1` and a number `l` of random subsets such that the approximation error is small
and the resulting degree `((q-1) l) ^ d` is at most `√m / 3`. -/
