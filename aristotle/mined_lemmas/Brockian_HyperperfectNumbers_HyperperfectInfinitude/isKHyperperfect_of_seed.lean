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

theorem isKHyperperfect_of_seed {m : ℕ} (h : HyperperfectSeed m) :
    IsKHyperperfect m ((m + 1) * (m * m + m + 1)) := by
  obtain ⟨hp, hq⟩ := h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (h0 ▸ hp) (by norm_num)
    · exact h0
  have hne : m + 1 ≠ m * m + m + 1 := by
    have hmm : 0 < m * m := Nat.mul_pos hm hm
    omega
  refine ⟨hm, ?_⟩
  rw [sigma1_mul_of_distinct_primes hp hq hne]
  ring

/-- Every seed gives a hyperperfect number. -/
