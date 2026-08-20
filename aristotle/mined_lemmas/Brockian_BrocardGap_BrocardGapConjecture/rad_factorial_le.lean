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

lemma rad_factorial_le (n : ℕ) : rad (n !) ≤ 4 ^ n := by
  have hsub : (n !).primeFactors ⊆ Finset.filter Nat.Prime (Finset.range (n + 1)) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := (Nat.Prime.dvd_factorial hpp).1 hdvd; omega, hpp⟩
  calc rad (n !) ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), p :=
        Finset.prod_le_prod_of_subset_of_one_le' hsub
          (fun i hi _ => (Finset.mem_filter.1 hi).2.one_lt.le)
    _ = primorial n := rfl
    _ ≤ 4 ^ n := primorial_le_4_pow n

/-! ### The gap -/

