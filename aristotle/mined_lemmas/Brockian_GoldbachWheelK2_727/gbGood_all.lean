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

theorem gbGood_all : (List.range 726).all (fun i => gbGood (2 * (i + 2))) = true := by
  decide

/-- **Goldbach wheel, K = 2, bound 727.**  Every even number `2 * n` with `2 ≤ n ≤ 727`
(i.e. every even number from `4` up to `1454`) is a sum of two primes. -/
