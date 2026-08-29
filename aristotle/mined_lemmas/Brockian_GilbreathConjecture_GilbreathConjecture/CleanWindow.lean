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

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.dupNamespace false

namespace Brockian
namespace GilbreathConjecture

/-!
## Setup

`gRow k n` is the `n`-th entry (0-indexed) of the `k`-th row of Gilbreath's triangle:
row `0` is the sequence of primes `2, 3, 5, 7, 11, …` and each subsequent row consists of the
absolute differences of consecutive entries of the previous row.

Gilbreath's conjecture states that every row of index `k ≥ 1` begins with `1`.
The conjecture is open; what is proved below is

* an unconditional verification for all rows of index `1 ≤ k ≤ 60`
  (`gilbreath_holds_below_61`), and
* the classical Odlyzko-style reduction (`GilbreathConjecture`): the conjecture follows from the
  hypothesis that for every `N ≥ 1` some row of index `k ≤ N` begins with `1` and has all of its
  next `N` entries equal to `0` or `2`.
-/

/-- The rows of Gilbreath's triangle: `gRow 0` enumerates the primes and
`gRow (k+1) n = |gRow k (n+1) - gRow k n|`. -/

def CleanWindow (k N : ℕ) : Prop :=
  gRow k 0 = 1 ∧ ∀ i, 1 ≤ i → i ≤ N → gRow k i = 0 ∨ gRow k i = 2

/-- The hypothesis used by Odlyzko's verification method: for every `N ≥ 1` there is a row of
index `k` with `1 ≤ k ≤ N` which begins with `1` and whose next `N` entries are all `0` or `2`. -/
