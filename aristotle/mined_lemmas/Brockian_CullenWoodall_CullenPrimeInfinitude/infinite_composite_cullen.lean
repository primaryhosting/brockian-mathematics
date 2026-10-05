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

(The header comment is placed immediately after `import Mathlib` because Lean 4
requires `import` commands to precede every other command, including module
docstrings; the header text itself is verbatim.)
-/

set_option maxHeartbeats 1000000

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem infinite_composite_cullen : {n : ℕ | ¬ (cullen n).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a + 5)
  exact ⟨p - 2, not_prime_cullen_sub_two hp (by omega), by omega⟩

/-!
## Reformulation of the Cullen prime infinitude conjecture

The conjecture that infinitely many Cullen numbers are prime is open.  The theorem
below is a Lean-checked *reduction*: it derives the infinitude of Cullen primes from
the (equivalent, but more directly attackable) statement that arbitrarily large
Cullen numbers have no prime factor below their square root.
-/

/-- The sieve-style hypothesis: arbitrarily large Cullen numbers have no prime factor
`p` with `p * p ≤ C n`. -/
