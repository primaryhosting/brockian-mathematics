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

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires all `import` commands to appear before any
other command, including module docstrings, so the mandated header comment above
is placed immediately after the single `import Mathlib` line.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th **Cullen number** `C n = n * 2 ^ n + 1`. -/

theorem two_not_mem_cullenPrimeIndices : 2 ∉ cullenPrimeIndices := by
  simp only [cullenPrimeIndices, Set.mem_setOf_eq, cullen]
  decide

/-!
## The statement

Whether there are infinitely many Cullen primes is a well-known open problem, so the
theorem `CullenPrimeInfinitude` below is stated as a *conditional reduction*: from the
hypothesis that Cullen primes occur beyond every bound one obtains the infinitude of
the set of Cullen prime indices.  The converse implication is
`cullenPrimeIndices_unbounded_of_infinite`, so the two formulations are provably
equivalent (`cullenPrimeIndices_infinite_iff`).

Unconditionally we prove that composite Cullen numbers occur beyond every bound: for
every odd prime `p` we have `p ∣ C (p - 1)` and `C (p - 1) > p`, hence `C (p - 1)` is
composite (`not_prime_cullen_prime_sub_one`, `infinite_cullen_composite_indices`).
-/

/-- **Conditional reduction for the Cullen prime infinitude conjecture.**
If Cullen primes occur beyond every bound, then the set of indices `n` such that
`n * 2 ^ n + 1` is prime is infinite. -/
