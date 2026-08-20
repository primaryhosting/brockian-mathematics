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

theorem head_one_of_row_zero_two :
    ∀ (m r : ℕ), G r 0 = 1 → (∀ i, 1 ≤ i → i ≤ m → G r i = 0 ∨ G r i = 2) →
      ∀ j ≤ m, G (r + j) 0 = 1 := by
  intro m
  induction m with
  | zero =>
      intro r h0 _ j hj
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      simpa using h0
  | succ m ih =>
      intro r h0 hrow j hj
      match j with
      | 0 => simpa using h0
      | (j + 1) =>
        have hj' : j ≤ m := by omega
        -- the next row again starts with `1` …
        have hnext0 : G (r + 1) 0 = 1 := by
          have h1 : G r 1 = 0 ∨ G r 1 = 2 := hrow 1 le_rfl (by omega)
          rw [G_succ, h0]
          exact dist_one_of_mem _ h1
        -- … and its first `m` entries again lie in `{0,2}`
        have hnextrow : ∀ i, 1 ≤ i → i ≤ m → G (r + 1) i = 0 ∨ G (r + 1) i = 2 := by
          intro i hi1 him
          have hA : G r i = 0 ∨ G r i = 2 := hrow i hi1 (by omega)
          have hB : G r (i + 1) = 0 ∨ G r (i + 1) = 2 := hrow (i + 1) (by omega) (by omega)
          rw [G_succ]
          exact dist_mem_of_mem _ _ hB hA
        have h := ih (r + 1) hnext0 hnextrow j hj'
        have hrw : r + (j + 1) = r + 1 + j := by omega
        rw [hrw]
        exact h

/-! ### The reduction -/

/-- The (numerically verified, but unproved) *Gilbreath data* hypothesis, in the form used by
Odlyzko: for every height `N ≥ 1` there is a row `r` with `1 ≤ r ≤ N` which starts with `1`
and whose next `N` entries all lie in `{0, 2}`.

Note that this is a genuinely stronger statement than the conjecture itself: it is a
horizontal assertion about a single, shallow row (`r ≤ N`) extending far to the right, and it
is exactly what the classical numerical verifications check.  In particular one cannot take
`r = N` for free — that would require row `N` to consist of a `1` followed by `N` entries
from `{0, 2}`, which is not a consequence of the conjecture. -/
