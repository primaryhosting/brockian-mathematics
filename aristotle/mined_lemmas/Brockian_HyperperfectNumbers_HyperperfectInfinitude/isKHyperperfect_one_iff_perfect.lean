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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

/-- `sigma1 n` is the sum of all divisors of `n`. -/

theorem isKHyperperfect_one_iff_perfect {n : ℕ} (hn : 0 < n) :
    IsKHyperperfect 1 n ↔ n.Perfect := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn]
  constructor
  · rintro ⟨-, h⟩
    simp only [sigma1, one_mul] at h
    omega
  · intro h
    refine ⟨Nat.one_pos, ?_⟩
    simp only [sigma1, one_mul]
    omega

/-- Since perfect numbers are hyperperfect, the (open) infinitude of perfect numbers is a second
sufficient condition for the infinitude of hyperperfect numbers. -/
