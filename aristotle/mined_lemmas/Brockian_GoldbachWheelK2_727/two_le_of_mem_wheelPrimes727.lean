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


theorem two_le_of_mem_wheelPrimes727 {p : Nat} (hp : p ∈ wheelPrimes727) : 2 ≤ p :=
  (prime_of_mem_wheelPrimes727 hp).1

/-- The wheel search: for every even `n` with `4 ≤ n ≤ 727` some wheel prime `p` has `n - p`
again a wheel prime. -/
