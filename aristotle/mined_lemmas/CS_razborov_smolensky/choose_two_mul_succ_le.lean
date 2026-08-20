import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma choose_two_mul_succ_le (m : ℕ) : (2 * m + 1).choose m ≤ 2 * Nat.centralBinom m := by
  cases m with
  | zero => simp [Nat.centralBinom]
  | succ j =>
      have h : (2 * (j + 1) + 1).choose (j + 1) = (2 * (j + 1)).choose j
          + (2 * (j + 1)).choose (j + 1) := by
        have : 2 * (j + 1) + 1 = (2 * (j + 1)) + 1 := rfl
        rw [this, Nat.choose_succ_succ]
      rw [h]
      have hmid : (2 * (j + 1)).choose j ≤ (2 * (j + 1)).choose (j + 1) := by
        have := Nat.choose_le_middle j (2 * (j + 1))
        simpa [Nat.mul_div_cancel_left] using this
      have hcb : (2 * (j + 1)).choose (j + 1) = Nat.centralBinom (j + 1) := by
        rw [Nat.centralBinom]
      omega

/-- The sum of the first `m + D + 1` binomial coefficients `C(2m+1, i)`. -/
