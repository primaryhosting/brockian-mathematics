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
# The Gilbreath triangle: definition and explicit values

Auxiliary file for `Brockian.GilbreathConjecture`.  It sets up the Gilbreath triangle of the
primes and records the explicit values of its first eleven rows (as far as they are
determined by the first `45` primes).
-/

namespace Brockian.GilbreathConjecture

/-- Row `n`, entry `k` of the Gilbreath triangle of the prime numbers:
row `0` is the sequence of primes, and each later row consists of the absolute values of the
differences of consecutive entries of the previous row. -/

theorem gilbreathConjecture_of_rowGood
    (H : ∀ N : ℕ, ∃ n m : ℕ, n ≤ N ∧ N ≤ n + m ∧ RowGood n m) :
    GilbreathConjecture := by
  intro N
  obtain ⟨n, m, h1, h2, hg⟩ := H (N + 1)
  have := hg.head (j := N + 1 - n) (by omega)
  rwa [show n + (N + 1 - n) = N + 1 by omega] at this

/-! ## An unconditional verification of the first rows

Row `10` of the triangle is `1, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 2, 0, 0, …`; its first `34`
entries after the leading `1` all lie in `{0, 2}`, so Odlyzko's criterion certifies rows
`10` through `44`.  Rows `1` through `9` are checked directly.
-/

