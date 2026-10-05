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

/-
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.TwinPrimes

open Nat

/-- `p` is a twin prime (the smaller member of a twin prime pair) if both `p` and `p + 2`
are prime. -/

theorem twinPrimes_infinite_iff :
    twinPrimes.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ IsTwinPrime p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro a
    obtain ⟨p, hlt, hp⟩ := h a
    exact ⟨p, hp, hlt⟩

/-! ### Clement's criterion

Clement's theorem: for `n ≥ 3`, the pair `(n, n + 2)` is a twin prime pair if and only if
`n * (n + 2)` divides `4 * ((n - 1)! + 1) + n`.  We prove this unconditionally; it converts the
twin prime conjecture into a purely arithmetic divisibility statement.
-/

/-- Auxiliary factorial identity: `(k + 4)! = (k + 4) * ((k + 3) * (k + 2)!)`. -/
