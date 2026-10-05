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

def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- `noFactorFrom f d n` checks, using `f` units of fuel, that no `k ≥ d` with `k * k ≤ n`
divides `n`.  Exhausting the fuel returns `false`, so a `true` answer always comes from a
completed search; this makes the test sound by construction. -/
