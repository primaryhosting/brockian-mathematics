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

A *Zumkeller number* is a positive integer whose divisors can be split into two sets with
equal sums.  Here we prove that an odd Zumkeller number must have at least three distinct
prime factors.

The argument: a Zumkeller number is perfect or abundant (`σ(n) ≥ 2n`), while an odd number
with at most two distinct prime factors `p < q` satisfies
`σ(n)/n < p/(p-1) · q/(q-1) ≤ (3/2)(5/4) < 2`, hence is deficient.
-/

open scoped BigOperators

set_option maxRecDepth 40000

namespace Brockian.ZumkellerNumbers

/-- `n` is a *Zumkeller number* if it is positive and its set of divisors can be split into
two parts having the same sum. -/

theorem two_mul_le_sigma_of_isZumkeller {n : ℕ} (hn : IsZumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hpos, S, hS, hsum⟩ := hn
  have hsplit : ∑ d ∈ n.divisors \ S, d + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hpos.ne'
  by_cases hnS : n ∈ S
  · have : n ≤ ∑ d ∈ S, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hnS
    omega
  · have hnT : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, hnS⟩
    have : n ≤ ∑ d ∈ n.divisors \ S, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hnT
    omega

/-- Geometric sum identity in `ℕ`. -/
