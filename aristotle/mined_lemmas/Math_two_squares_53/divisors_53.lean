import Mathlib
import RequestProject.TwoSquares53

/-!
# Two Squares 53 — Mathlib restatement

The target theorem `Math.two_squares_53` lives in `RequestProject/TwoSquares53.lean`,
which is import-free (its statement uses the self-contained predicate `Math.IsPrimeNat`).
Here we record that this predicate agrees with Mathlib's `Nat.Prime`, and restate the
result in Mathlib terms.
-/

namespace Math

/-- `Math.IsPrimeNat` agrees with Mathlib's `Nat.Prime`. -/

theorem divisors_53 : ∀ m, m ∣ 53 → m = 1 ∨ m = 53 := by
  have key : ∀ m ≤ 53, m ∣ 53 → m = 1 ∨ m = 53 := by decide
  intro m hm
  exact key m (Nat.le_of_dvd (by decide) hm) hm

/-- `53` is prime. -/
