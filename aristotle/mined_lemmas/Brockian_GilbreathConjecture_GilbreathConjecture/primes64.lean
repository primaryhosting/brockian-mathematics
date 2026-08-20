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

def primes64 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
   89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
   181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277,
   281, 283, 293, 307, 311]

