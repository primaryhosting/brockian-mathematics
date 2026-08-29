import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib bridge

The target theorem `Brockian.GoldbachWheelK2_727` lives in a Mathlib-free file (a module
docstring may not precede `import`, so the required header comment forces that file to be
import-free).  Here we identify the primality predicate used there with Mathlib's
`Nat.Prime` and restate the result accordingly.
-/

namespace Brockian

/-- The from-first-principles primality predicate agrees with Mathlib's `Nat.Prime`. -/

def findPrimePair : Nat → Nat → Nat → Nat
  | 0, p, _ => p
  | (f + 1), p, m => if isPrimeFast p && isPrimeFast (m - p) then p else findPrimePair f (p + 1) m

/-- The small prime in the Goldbach decomposition of `m` found by the search. -/
