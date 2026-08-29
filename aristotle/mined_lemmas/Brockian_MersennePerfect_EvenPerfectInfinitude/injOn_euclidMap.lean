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
/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is wrapped in an outer block comment because Lean 4 requires
-- `import` commands to precede every other command, including module docstrings.)
-/

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
Whether there are infinitely many even perfect numbers is an open problem (it is equivalent
to the infinitude of Mersenne primes).  What is proved here is exactly that equivalence, i.e.
a Lean-checked reduction of the conjecture:

  `{n | Even n ∧ n.Perfect}.Infinite ↔ {p | (mersenne p).Prime}.Infinite`

The proof goes through the Euclid–Euler theorem: the map `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)`
is a bijection from the set of Mersenne exponents `p` with `2 ^ p - 1` prime onto the set of
even perfect numbers.
-/

namespace Brockian.MersennePerfect

open Set

/-- The set of exponents `p` for which `mersenne p = 2 ^ p - 1` is prime. -/

theorem injOn_euclidMap : InjOn euclidMap mersenneExponents := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hab (euclidMap_lt_euclidMap (one_le_of_mem_mersenneExponents ha) h).ne
  · exact absurd hab.symm (euclidMap_lt_euclidMap (one_le_of_mem_mersenneExponents hb) h).ne

/-- **Euclid's direction**: Euclid's map sends Mersenne exponents to even perfect numbers. -/
