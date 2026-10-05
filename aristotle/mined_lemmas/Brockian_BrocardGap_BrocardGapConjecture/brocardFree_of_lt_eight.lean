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

theorem brocardFree_of_lt_eight (n : ℕ) (hn : n < 8) (h4 : n ≠ 4) (h5 : n ≠ 5) (h7 : n ≠ 7) :
    BrocardFree n := by
  interval_cases n
  · exact brocardFree_of_mod 0 3 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 1 3 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 2 5 3 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 3 5 2 (by norm_num) (by rfl) (by decide)
  · exact absurd rfl h4
  · exact absurd rfl h5
  · exact brocardFree_of_mod 6 11 6 (by norm_num) (by rfl) (by decide)
  · exact absurd rfl h7

/-- The three known solutions of Brocard's problem. -/
