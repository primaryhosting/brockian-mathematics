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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is *Zumkeller* if it is positive and its set of divisors can be
split into two parts with equal sums. -/

theorem sum_divisors_lt_of_card_le_two {n : ℕ} (hn : n ≠ 0) (hodd : Odd n)
    (hcard : n.primeFactors.card ≤ 2) : ∑ d ∈ n.divisors, d < 2 * n := by
  rcases Finset.eq_empty_or_nonempty n.primeFactors with hemp | hne
  · have hone : n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp hemp with h | h <;> omega
    subst hone
    simp
  · have h1 := prod_sub_one_mul_sum_divisors_lt hn hne
    have h2 := prod_primeFactors_le hodd hcard
    have key : (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
        < (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by
      calc (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
          < (∏ p ∈ n.primeFactors, p) * n := h1
        _ ≤ (2 * ∏ p ∈ n.primeFactors, (p - 1)) * n := Nat.mul_le_mul_right _ h2
        _ = (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by ring
    exact lt_of_mul_lt_mul_left key (Nat.zero_le _)

/-- **Odd Zumkeller From 3 Structure.** Every odd Zumkeller number has at least three
distinct prime factors. -/
