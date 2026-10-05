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

def noFactorFrom : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | (f + 1), d, n =>
      if n < d * d then true else if n % d == 0 then false else noFactorFrom f (d + 1) n

/-- A kernel-friendly primality test: trial division up to the square root. -/
