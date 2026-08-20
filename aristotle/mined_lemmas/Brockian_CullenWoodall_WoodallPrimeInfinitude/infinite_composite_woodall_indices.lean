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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; note `W 0 = 0`). -/

theorem infinite_composite_woodall_indices :
    {n : ℕ | 0 < n ∧ ¬ (woodall n).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  exact ⟨6 * (a + 1) + 4, ⟨by omega, not_prime_woodall_of_mod_six (Or.inl (by omega))⟩, by omega⟩

/-! ## The main reduction -/

/-- **Reduction of the conjecture to an index statement.** There are infinitely many Woodall
primes if and only if for every bound `N` there is some index `n > N` with `n * 2 ^ n - 1`
prime. -/
