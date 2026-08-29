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

open Finset

/-- `sigma n` is the sum of all divisors of `n`. -/

theorem hyperperfect_examples :
    ({6, 21, 28, 301, 325, 496, 697} : Set ℕ) ⊆ Hyperperfect := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, isHyperperfect_one_six⟩
  · exact ⟨2, isHyperperfect_two_21⟩
  · exact ⟨1, by norm_num, by norm_num, by decide⟩
  · exact ⟨6, isHyperperfect_six_301⟩
  · exact ⟨3, by norm_num, by norm_num, by decide⟩
  · exact ⟨1, by norm_num, by norm_num, by decide⟩
  · exact ⟨12, by norm_num, by norm_num, by decide⟩

/-! ## The main conditional reduction -/

/-- **Hyperperfect Infinitude (conditional).**
If there are infinitely many primes `p` for which `p² - p + 1` is also prime, then there
are infinitely many hyperperfect numbers.  (Unconditional infinitude of hyperperfect
numbers is an open problem; already the case `k = 1`, i.e. perfect numbers, is open.) -/
