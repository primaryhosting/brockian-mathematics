import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib restatement

The target theorem `Brockian.GoldbachWheelK2_727` is stated in a self-contained way (its own
primality predicate `Brockian.IsPrime`), because the required file header must be the very first
thing in that file and Lean does not accept `import` after it.  Here we bridge that predicate to
`Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian


theorem nat_prime_iff_isPrime {p : ℕ} : Nat.Prime p ↔ IsPrime p :=
  Nat.prime_def

/-- Mathlib restatement: every even `n` with `4 ≤ n ≤ 727` is a sum of two primes. -/
