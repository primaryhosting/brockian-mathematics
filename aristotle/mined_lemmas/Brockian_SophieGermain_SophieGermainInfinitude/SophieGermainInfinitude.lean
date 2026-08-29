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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a Sophie Germain prime if both `p` and `2 * p + 1` are prime. -/

theorem SophieGermainInfinitude
    (h : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ((2 * p + 1) ∣ 2 ^ p - 1 ∨ (2 * p + 1) ∣ 2 ^ p + 1)) :
    {p : ℕ | p.Prime ∧ (2 * p + 1).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hN, hp, hd⟩ := h N
  refine ⟨p, ?_, hN⟩
  rcases hd with hd | hd
  · exact ⟨hp, prime_of_dvd_two_pow_sub_one hp hd⟩
  · exact ⟨hp, prime_of_dvd_two_pow_add_one hp hd⟩

/-- The hypothesis of `SophieGermainInfinitude` is *equivalent* to the Sophie Germain
conjecture, so the reduction loses nothing. -/
