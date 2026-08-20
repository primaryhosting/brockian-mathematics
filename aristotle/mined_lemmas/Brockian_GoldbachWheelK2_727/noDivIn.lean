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


def noDivIn (p : Nat) : Nat → Bool
  | 0 => true
  | 1 => true
  | (k + 2) => (p % (k + 2) != 0) && noDivIn p (k + 1)

/-- A Boolean primality test by trial division. -/
