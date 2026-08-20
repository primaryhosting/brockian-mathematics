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


def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- The `K = 2` Goldbach property: `n` is a sum of two primes. -/
