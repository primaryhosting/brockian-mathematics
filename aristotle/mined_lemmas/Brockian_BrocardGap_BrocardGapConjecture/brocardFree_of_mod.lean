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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BrocardGap

open Nat

/-- `BrocardFree n` says that `n ! + 1` is not a perfect square, i.e. `n` is not a
solution of Brocard's problem. -/

theorem brocardFree_of_mod (n q r : ℕ) (hq : 0 < q) (hr : (n ! + 1) % q = r)
    (h : ((List.range q).all fun x => decide (x * x % q ≠ r)) = true) : BrocardFree n := by
  intro m hm
  have hmem : m % q ∈ List.range q := List.mem_range.mpr (Nat.mod_lt _ hq)
  have hx : (m % q) * (m % q) % q ≠ r := by
    have := List.all_eq_true.mp h (m % q) hmem
    simpa using this
  apply hx
  have hsq : m ^ 2 % q = (m % q) * (m % q) % q := by
    rw [pow_two, Nat.mul_mod]
  rw [← hsq, ← hm, hr]

set_option maxRecDepth 40000

/-- Apart from `n = 4, 5, 7`, no `n < 8` solves Brocard's problem. -/
