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
open scoped Matrix

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

/-- The Toffoli (CCNOT) gate as an `8 × 8` complex matrix, in the standard
computational basis ordering `|a b c⟩ ↦ 4a + 2b + c`.  It is the identity except
that it swaps the basis states `|110⟩` and `|111⟩`. -/

lemma toffoli_bitIdx (a b c a' b' c' : Fin 2) :
    toffoli (bitIdx a b c) (bitIdx a' b' c') =
      if a' = a ∧ b' = b ∧ c' = c + a * b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
    norm_num [toffoli, bitIdx, Fin.ext_iff]
  all_goals decide

/-- The Toffoli matrix is the permutation matrix of the transposition of the
basis indices `6 = |110⟩` and `7 = |111⟩`. -/
