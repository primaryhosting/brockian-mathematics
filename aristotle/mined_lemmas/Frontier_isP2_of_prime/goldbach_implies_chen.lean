import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires the `import` commands to come first in a module, so the
prescribed header comment above is placed immediately after `import Mathlib`.

Contents:

* `Frontier.IsP2`, `Frontier.ChenRepresentable`, `Frontier.ChenStatement` : the formal statement
  of Chen's theorem ("every sufficiently large even number is `p + q` with `p` prime and `q`
  having at most two prime factors").
* `Frontier.Chen_base_case` : an unconditional, kernel-checked verification of the conclusion for
  all even `n` with `4 ≤ n ≤ 500`.
* `Frontier.Chen_theorem` : a Lean-checked reduction of the full statement to the sieve statement
  that Chen's method produces (a prime `p` with all prime factors of `n - p` exceeding `n ^ (1/3)`).
* `Frontier.goldbach_implies_chen` : the (easier) reduction of Chen's statement to Goldbach's
  conjecture.
-/

open ArithmeticFunction

namespace Frontier

/-- `q` is an *almost prime of order 2* (a `P₂` number): `q > 1` and `q` has at most two prime
factors counted with multiplicity (`Ω q ≤ 2`), i.e. `q` is a prime or a product of two primes. -/

theorem goldbach_implies_chen : GoldbachStatement → ChenStatement := by
  intro hG
  refine ⟨4, fun n hn hev => ?_⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := hG n hn hev
  exact chenRepresentable_of_sum_two_primes hp hq hpq

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

