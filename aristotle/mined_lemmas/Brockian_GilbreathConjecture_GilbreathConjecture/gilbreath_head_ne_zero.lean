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

theorem gilbreath_head_ne_zero (n : ℕ) : gilbreath (n + 1) 0 ≠ 0 := by
  have := gilbreath_head_odd n
  rw [Nat.odd_iff] at this
  omega

/-! ## Odlyzko's criterion (conditional reduction)

If a row starts with `1` and its next `m` entries all lie in `{0, 2}`, then the same is true
of the next row with `m - 1` in place of `m`.  Consequently the next `m` rows all start
with `1`, and Gilbreath's conjecture reduces to finding, for every `N`, such a row `n ≤ N`
whose run of `{0,2}`-entries is long enough to reach `N`.
-/

/-- `RowGood n m` says that row `n` starts with `1` and its entries at positions
`1, …, m` all belong to `{0, 2}`. -/
