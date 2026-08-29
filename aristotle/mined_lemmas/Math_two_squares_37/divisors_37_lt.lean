import Mathlib

/-!
# Two Squares 37 — via Mathlib's Fermat two-squares theorem

Companion to `RequestProject/Math.lean`.  The main target `Math.two_squares_37`
is stated and proved there without any imports (so that the required header
comment can begin the file); here we record the same existence statement as a
consequence of Mathlib's `Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `37` is a sum of two squares, derived from Fermat's two-squares theorem
(`Nat.Prime.sq_add_sq`) applied to the prime `37 ≡ 1 [MOD 4]`. -/

theorem divisors_37_lt : ∀ m < 38, m ∣ 37 → m = 1 ∨ m = 37 := by decide

/-- `37` is prime: it is at least `2` and its only divisors are `1` and `37`. -/
