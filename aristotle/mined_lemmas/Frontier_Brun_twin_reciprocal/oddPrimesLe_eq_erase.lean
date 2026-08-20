import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma oddPrimesLe_eq_erase (z : ℕ) :
    oddPrimesLe z = (Nat.primesBelow (z + 1)).erase 2 := by
  ext p
  rw [mem_oddPrimesLe, Finset.mem_erase, Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hle, hp, hne⟩
    exact ⟨hne, by omega, hp⟩
  · rintro ⟨hne, hlt, hp⟩
    exact ⟨by omega, hp, hne⟩

/-- The main term of the sieve: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 4 e² / (log z)²`. -/
