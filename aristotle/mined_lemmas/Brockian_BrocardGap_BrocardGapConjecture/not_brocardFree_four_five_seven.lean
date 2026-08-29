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

theorem not_brocardFree_four_five_seven :
    ¬ BrocardFree 4 ∧ ¬ BrocardFree 5 ∧ ¬ BrocardFree 7 := by
  refine ⟨fun h => h 5 ?_, fun h => h 11 ?_, fun h => h 71 ?_⟩ <;> rfl

/-- **Partial verification.** No `n` with `8 ≤ n ≤ 100` solves Brocard's problem. -/
