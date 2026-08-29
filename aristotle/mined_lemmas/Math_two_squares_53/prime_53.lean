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

theorem prime_53 : IsPrimeNat 53 := ⟨by decide, divisors_53⟩

/-- **Two squares for 53**: the prime `53` is a sum of two squares,
namely `53 = 7 ^ 2 + 2 ^ 2`. -/
