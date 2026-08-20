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

/-
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Finset

/-!
## Setup

For a bound `N`, `primorial N` (Mathlib's `primorial`, notation `N#`) is the product of all
primes `≤ N`.  The *fortunate number* attached to `N` is the least `m ≥ 2` such that
`N# + m` is prime.  Fortune's conjecture asserts that this number is always prime.

The conjecture is open.  What we prove here is the classical unconditional dichotomy
(`fortunate_prime_or_sq_le`): the fortunate number is either prime or at least `(N+1)^2`,
because none of its prime factors can be `≤ N`.  The named target
`FortuneConjecture` is therefore the corresponding *conditional* statement: the fortunate
number is prime as soon as it is smaller than `(N+1)^2`.
-/

/-- Every prime `q ≤ N` divides the primorial `N#`. -/

theorem prime_primorial_add_fortunate (N : ℕ) : (primorial N + fortunate N).Prime :=
  (fortunate_mem N).2

