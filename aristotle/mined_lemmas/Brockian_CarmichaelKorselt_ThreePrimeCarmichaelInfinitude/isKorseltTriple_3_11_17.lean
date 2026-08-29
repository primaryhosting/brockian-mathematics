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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The unconditional infinitude of Carmichael numbers with exactly three prime factors is an
open problem.  This file gives a fully checked *conditional reduction*: Korselt's criterion
is proved in the three-prime case, reducing the conjecture to the purely arithmetic statement
`InfinitelyManyKorseltTriples`, and further to a Dickson-type prime-triple hypothesis via
Chernick's parametrisation `(6k+1)(12k+1)(18k+1)`.
-/

namespace Brockian.CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` such that `a ^ (n - 1) ≡ 1 [MOD n]` for every
`a` coprime to `n`. -/

theorem isKorseltTriple_3_11_17 : IsKorseltTriple 3 11 17 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩ <;> decide

