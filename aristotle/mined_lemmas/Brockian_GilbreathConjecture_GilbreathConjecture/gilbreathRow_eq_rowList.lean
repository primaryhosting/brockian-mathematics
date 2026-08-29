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

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Brockian
namespace GilbreathConjecture

/-! ## The Gilbreath triangle and the statement of the conjecture -/

/-- `gilbreathRow n k` is the `k`-th entry (0-indexed) of the `n`-th row of the
Gilbreath triangle: row `0` is the sequence of primes `2, 3, 5, 7, 11, ...` and each
subsequent row is obtained by taking absolute values of consecutive differences. -/

theorem gilbreathRow_eq_rowList (n k : ℕ) (h : k + n < 109) :
    gilbreathRow n k = (rowList n).getD k 0 := by
  induction n generalizing k with
  | zero => exact nth_prime_eq_primeList k (by omega)
  | succ n ih =>
      have hlen : k + 1 < (rowList n).length := by rw [rowList_length]; omega
      rw [gilbreathRow_succ, ih (k + 1) (by omega), ih k (by omega), rowList,
        diffs_getD (rowList n) k hlen]

/-- A `GoodRow` fact can be read off from the computable model. -/
