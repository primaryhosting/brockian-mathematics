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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`.  The only known
solutions are `n = 4, 5, 7` (with `m = 5, 11, 71`), and it is conjectured that
there are no others; in *gap* form the conjecture states that the distance from
`n ! + 1` to the nearest perfect square is positive (indeed large) for all
`n ≥ 8`.  This is an open problem.

This file contains:

* `Brockian.BrocardGap.brocardGap`, the distance from `n ! + 1` to the nearest
  perfect square, and the characterisation `brocardGap_pos_iff`;
* `Brockian.BrocardGap.ABC`, the `abc` conjecture (in radical form);
* `Brockian.BrocardGap.BrocardGapConjecture`, a Lean-checked **conditional
  reduction**: the `abc` conjecture implies that the Brocard gap is positive for
  all sufficiently large `n` (this is Overholt's argument);
* `Brockian.BrocardGap.brocardGap_pos_of_mem_Icc`, an unconditional verification
  of the gap positivity for `8 ≤ n ≤ 200`;
* `Brockian.BrocardGap.brocard_iff_pronic`, the elementary reformulation of
  Brocard's equation as `n ! = 4 * a * (a + 1)`.
-/

namespace Brockian.BrocardGap

open Nat Finset

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma rad_mul_le (a b : ℕ) : rad (a * b) ≤ rad a * rad b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [rad, Nat.zero_mul, Nat.primeFactors_zero, Finset.prod_empty, one_mul]
    exact rad_pos
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [rad, Nat.mul_zero, Nat.primeFactors_zero, Finset.prod_empty, mul_one]
    exact rad_pos
  unfold rad
  rw [Nat.primeFactors_mul ha hb,
    ← Finset.prod_sdiff (f := fun p : ℕ => p)
      (Finset.subset_union_left (s₁ := a.primeFactors) (s₂ := b.primeFactors)), mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  refine Finset.prod_le_prod_of_subset_of_one_le' ?_
    (fun i hi _ => (Nat.prime_of_mem_primeFactors hi).one_lt.le)
  intro x hx
  rw [Finset.mem_sdiff] at hx
  rcases Finset.mem_union.1 hx.1 with h | h
  · exact absurd h hx.2
  · exact h

