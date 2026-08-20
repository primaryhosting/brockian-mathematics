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

theorem two_mul_le_sum_divisors_of_zumkeller {n : ℕ} (h : Zumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hn, S, hS, hsum⟩ := h
  have hsplit : ∑ d ∈ n.divisors \ S, d + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  by_cases hnS : n ∈ S
  · have : n ≤ ∑ d ∈ S, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hnS
    omega
  · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, hnS⟩
    have : n ≤ ∑ d ∈ n.divisors \ S, d :=
      Finset.single_le_sum (fun i _ => Nat.zero_le i) hmem'
    omega

/-- Key bound: `(∏ (p-1)) * σ n < (∏ p) * n`, the products being over the prime factors of `n`. -/
