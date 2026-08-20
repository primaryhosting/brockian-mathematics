import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma centralBinom_sq_le (m : ℕ) : (Nat.centralBinom m) ^ 2 * (m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp [Nat.centralBinom]
  | succ m ih =>
      have hrec : (m + 1) * (m + 1).centralBinom = 2 * (2 * m + 1) * m.centralBinom :=
        Nat.succ_mul_centralBinom_succ m
      -- multiply the goal by `(m+1)^3`
      have key : ((m + 1) * (m + 1).centralBinom) ^ 2 * (m + 2) * (m + 1)
          ≤ 16 ^ (m + 1) * (m + 1) ^ 3 := by
        rw [hrec]
        have h1 : (2 * (2 * m + 1) * m.centralBinom) ^ 2 * (m + 2) * (m + 1)
            = (4 * (2 * m + 1) ^ 2 * (m + 2)) * ((m.centralBinom ^ 2) * (m + 1)) := by ring
        rw [h1]
        have h2 : (4 * (2 * m + 1) ^ 2 * (m + 2)) * ((m.centralBinom ^ 2) * (m + 1))
            ≤ (4 * (2 * m + 1) ^ 2 * (m + 2)) * 16 ^ m := Nat.mul_le_mul_left _ ih
        refine h2.trans ?_
        have h3 : 4 * (2 * m + 1) ^ 2 * (m + 2) ≤ 16 * (m + 1) ^ 3 := by nlinarith
        calc (4 * (2 * m + 1) ^ 2 * (m + 2)) * 16 ^ m
            ≤ (16 * (m + 1) ^ 3) * 16 ^ m := Nat.mul_le_mul_right _ h3
          _ = 16 ^ (m + 1) * (m + 1) ^ 3 := by ring
      have hpos : 0 < (m + 1) ^ 2 := by positivity
      have : ((m + 1).centralBinom ^ 2 * (m + 2)) * (m + 1) ^ 3
          ≤ 16 ^ (m + 1) * (m + 1) ^ 3 := by
        calc ((m + 1).centralBinom ^ 2 * (m + 2)) * (m + 1) ^ 3
            = ((m + 1) * (m + 1).centralBinom) ^ 2 * (m + 2) * (m + 1) := by ring
          _ ≤ 16 ^ (m + 1) * (m + 1) ^ 3 := key
      have h4 : 0 < (m + 1) ^ 3 := by positivity
      exact Nat.le_of_mul_le_mul_right this h4

