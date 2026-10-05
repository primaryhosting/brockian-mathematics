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

theorem diffs_getD : ∀ (l : List ℕ) (k : ℕ), k + 1 < l.length →
    (diffs l).getD k 0 = Nat.dist (l.getD (k + 1) 0) (l.getD k 0)
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | _ :: _ :: _, 0, _ => by simp [diffs]
  | _ :: b :: t, (k + 1), h => by
      simp only [diffs, List.getD_cons_succ]
      exact diffs_getD (b :: t) k (by simpa using h)

/-- The first `109` primes. -/
