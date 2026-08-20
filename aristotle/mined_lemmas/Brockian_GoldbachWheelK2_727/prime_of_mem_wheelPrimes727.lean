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


theorem prime_of_mem_wheelPrimes727 {p : Nat} (hp : p ∈ wheelPrimes727) : IsPrime p :=
  isPrime_of_isPrimeB (List.all_eq_true.mp wheelPrimes727_isPrimeB p hp)

/-- Every entry of the wheel is at least `2`. -/
