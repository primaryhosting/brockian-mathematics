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

def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- Every divisor of `53` is `1` or `53` (checked by decision procedure on the
finitely many candidates `m ≤ 53`, using that a divisor of a positive number
is at most that number). -/
