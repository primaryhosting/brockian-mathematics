/-
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

open Matrix

/-- The Toffoli (CCNOT) gate as an explicit `8 × 8` complex matrix, in the standard
computational-basis ordering `|000⟩, |001⟩, …, |111⟩`: it is the identity except that the
last two basis states `|110⟩` and `|111⟩` are exchanged. -/

theorem toffoliPerm_idx (a b c : Bool) :
    toffoliPerm (idx a b c) = idx a b (xor c (a && b)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- `toffoli` is the permutation matrix of `toffoliPerm`. -/
