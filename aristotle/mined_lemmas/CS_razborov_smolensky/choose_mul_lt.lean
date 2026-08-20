import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma choose_mul_lt {m D : ℕ} (h9 : 9 * D ^ 2 ≤ m) :
    3 * (D * ((2 * m + 1).choose m)) < 2 * 4 ^ m := by
  have hch : (2 * m + 1).choose m ≤ 2 * Nat.centralBinom m := choose_two_mul_succ_le m
  have hcb : (Nat.centralBinom m) ^ 2 * (m + 1) ≤ 16 ^ m := centralBinom_sq_le m
  have h16 : 0 < (16 : ℕ) ^ m := by positivity
  have hsq : (3 * (D * ((2 * m + 1).choose m))) ^ 2 < (2 * 4 ^ m) ^ 2 := by
    have h1 : (3 * (D * ((2 * m + 1).choose m))) ^ 2
        ≤ 9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2) := by
      have h2 : ((2 * m + 1).choose m) ^ 2 ≤ 4 * (Nat.centralBinom m) ^ 2 := by
        calc ((2 * m + 1).choose m) ^ 2 ≤ (2 * Nat.centralBinom m) ^ 2 :=
              Nat.pow_le_pow_left hch 2
          _ = 4 * (Nat.centralBinom m) ^ 2 := by ring
      calc (3 * (D * ((2 * m + 1).choose m))) ^ 2
          = 9 * D ^ 2 * ((2 * m + 1).choose m) ^ 2 := by ring
        _ ≤ 9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2) := Nat.mul_le_mul_left _ h2
    have h3 : (9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2)) * (m + 1) ≤ 4 * m * 16 ^ m := by
      calc (9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2)) * (m + 1)
          = (4 * (9 * D ^ 2)) * ((Nat.centralBinom m) ^ 2 * (m + 1)) := by ring
        _ ≤ (4 * (9 * D ^ 2)) * 16 ^ m := Nat.mul_le_mul_left _ hcb
        _ ≤ (4 * m) * 16 ^ m := Nat.mul_le_mul_right _ (by omega)
    have h4 : (2 * 4 ^ m) ^ 2 * (m + 1) = 4 * (m + 1) * 16 ^ m := by
      have h5 : (4 : ℕ) ^ m * 4 ^ m = 16 ^ m := by
        rw [← mul_pow]; norm_num
      calc (2 * 4 ^ m) ^ 2 * (m + 1) = 4 * (m + 1) * (4 ^ m * 4 ^ m) := by ring
        _ = 4 * (m + 1) * 16 ^ m := by rw [h5]
    have h5 : (3 * (D * ((2 * m + 1).choose m))) ^ 2 * (m + 1) < (2 * 4 ^ m) ^ 2 * (m + 1) := by
      calc (3 * (D * ((2 * m + 1).choose m))) ^ 2 * (m + 1)
          ≤ (9 * D ^ 2 * (4 * (Nat.centralBinom m) ^ 2)) * (m + 1) := Nat.mul_le_mul_right _ h1
        _ ≤ 4 * m * 16 ^ m := h3
        _ < 4 * (m + 1) * 16 ^ m := by
            have h6 : 4 * m < 4 * (m + 1) := by omega
            exact (Nat.mul_lt_mul_right h16).2 h6
        _ = (2 * 4 ^ m) ^ 2 * (m + 1) := h4.symm
    exact lt_of_mul_lt_mul_right h5 (Nat.zero_le _)
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hsq

/-- The final counting contradiction. -/
