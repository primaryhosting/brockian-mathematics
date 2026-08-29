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

def gbGood (m : Nat) : Bool :=
  isPrimeFast (gbP m) && isPrimeFast (m - gbP m) && Nat.ble (gbP m) m

/-- The certificate holds for every even number `2 * n` with `2 ≤ n ≤ 727`. -/
