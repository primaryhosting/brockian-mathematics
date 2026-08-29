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

set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

open Finset

/-- A positive natural number `n` is *Zumkeller* if its set of divisors can be split into
two blocks with equal sums. -/

theorem two_mul_le_sigma_of_zumkeller {n : ℕ} (hz : Zumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hn, S, hS, hsum⟩ := hz
  have hsplit : ∑ d ∈ n.divisors \ S, d + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have key : n ≤ ∑ d ∈ S, d := by
    by_cases h : n ∈ S
    · exact Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) h
    · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, h⟩
      have := Finset.single_le_sum (f := fun d => (d : ℕ)) (fun i _ => Nat.zero_le i) hmem'
      simp only at this
      omega
  omega

/-- Geometric-sum identity for the divisor sum of a prime power:
`(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/
