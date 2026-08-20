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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset

/-- A natural number `n` is *practical* if it is positive and every `m ≤ n` can be written
as a sum of distinct divisors of `n`. -/

lemma practical_two_pow (k : ℕ) : Practical (2 ^ k) := by
  refine ⟨Nat.two_pow_pos k, ?_⟩
  intro m hm
  rcases lt_or_eq_of_le hm with h | h
  · obtain ⟨S, hS, hSsum⟩ := pow_two_rep k m h
    refine ⟨S, ?_, hSsum⟩
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hS hx)
    exact Nat.mem_divisors.mpr ⟨pow_dvd_pow 2 (le_of_lt (Finset.mem_range.mp hj)),
      (Nat.two_pow_pos k).ne'⟩
  · exact ⟨{2 ^ k}, by simp [Nat.mem_divisors], by simpa using h.symm⟩

/-! ### The family `N i = 2 ^ (2 ^ i + 1) - 2` -/

/-- Fermat-type factors `F i = 2 ^ (2 ^ i) + 1`. -/
