import Mathlib
import RequestProject.TwoSquares13

/-!
# Two Squares 13 (Mathlib phrasing)

A companion to `RequestProject/TwoSquares13.lean`, restating the result with
Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `13` is a sum of two squares: `13 = 2 ^ 2 + 3 ^ 2`. -/

theorem divisors_13 : ∀ m : Nat, m ∣ 13 → m = 1 ∨ m = 13 := by
  have key : ∀ m : Nat, m < 14 → m ∣ 13 → m = 1 ∨ m = 13 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

/-- **Two squares for 13.** The number `13` is prime (it is at least `2` and its only
divisors are `1` and itself) and it is a sum of two squares, namely `13 = 2 ^ 2 + 3 ^ 2`. -/
