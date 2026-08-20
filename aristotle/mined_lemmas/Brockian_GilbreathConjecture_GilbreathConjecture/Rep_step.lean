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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Gilbreath's conjecture concerns the triangle of iterated absolute differences of the
sequence of primes.  Writing `G 0 n` for the `n`-th prime (`2, 3, 5, 7, …`) and

  `G (k+1) n = |G k (n+1) - G k n|`,

the conjecture asserts that every row after the zeroth begins with `1`:

  `∀ k ≥ 1, G k 0 = 1`.

This is an open problem.  What is proved here is the classical *reduction* (going back to
Killgrove–Ralston and Odlyzko): the conjecture follows from the purely "local" statement that
for every `N` some row `r ≤ N` begins with a `1` followed by at least `N` entries taken
from `{0, 2}`.  That statement (`GilbreathData` below) has been verified numerically to very
large heights; it is *not* proved here, and it is carried as an explicit hypothesis of the
main theorem `GilbreathConjecture`.

The mathematical content that *is* proved unconditionally is:

* `head_one_of_row_zero_two` : if a row `r` reads `1, e₁, …, e_m` with every `eᵢ ∈ {0, 2}`,
  then each of the rows `r, r+1, …, r+m` begins with `1`.  This is the "Gilbreath sequence"
  propagation lemma, the engine of the reduction.
* `GilbreathConjecture` : the conjecture, conditional on `GilbreathData`.
* `gilbreath_head_eq_one_of_le_63` : an unconditional, kernel-checked verification of the
  first `63` rows.
-/

namespace Brockian.GilbreathConjecture

/-- `nthPrime n` is the `n`-th prime number, with `nthPrime 0 = 2`. -/

lemma Rep_step {k n : ℕ} {l : List ℕ} (hl : Rep k n l) : Rep (k + 1) n (step l) := by
  intro i hi
  have hi' : i < l.length := by
    simp only [step, List.length_zipWith, List.length_tail] at hi
    omega
  have hi'' : i < l.tail.length := by
    simp only [step, List.length_zipWith, List.length_tail] at hi
    simp only [List.length_tail]
    omega
  have hsucc : i + 1 < l.length := by
    simp only [List.length_tail] at hi''
    omega
  simp only [step, List.getElem_zipWith, List.getElem_tail hi'']
  rw [hl i hi', hl (i + 1) hsucc, G_succ, Nat.add_assoc]

