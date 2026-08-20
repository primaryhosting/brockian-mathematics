import Brockian.CullenWoodall

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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Mathlib (as of this toolchain) contains no material on Cullen or Woodall numbers -- a search
for `Woodall` returns nothing -- so the notions below are developed from scratch.  The Mathlib
results actually used are `strictMono_nat_of_lt_succ`, `Nat.sub_lt_sub_right`,
`Set.infinite_of_not_bddAbove` and `Set.Infinite.exists_gt`.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; for `n ≥ 1`
this agrees with the usual integer definition). -/

lemma seven_mem_woodallPrimes : 7 ∈ WoodallPrimes :=
  ⟨by norm_num, 2, by norm_num, woodall_two⟩

/-!
## Main conditional theorem

Whether infinitely many Woodall numbers are prime is an open problem, so we prove the
statement in conditional form: if Woodall primes occur at arbitrarily large indices, then
there are infinitely many Woodall *primes*.  The content of the reduction is that
`n ↦ W n` is strictly increasing for `n ≥ 1` and `W n ≥ n`, so the resulting set of primes
is unbounded.
-/

/-- **Woodall prime infinitude (conditional).**
If for every `N` there is an index `n > N` with `W n = n * 2 ^ n - 1` prime, then the set of
Woodall primes is infinite.  (The unconditional statement is an open problem.) -/
