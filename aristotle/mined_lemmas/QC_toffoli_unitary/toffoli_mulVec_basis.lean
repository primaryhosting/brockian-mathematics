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

open scoped BigOperators
open scoped Classical
open Matrix

set_option maxHeartbeats 4000000

namespace QC

/-- The classical action of the Toffoli (CCNOT) gate on the eight computational basis
states of three qubits, indexed by `Fin 8` via `i = 4*b₂ + 2*b₁ + b₀`.  It flips the
target bit `b₀` exactly when both control bits `b₂`, `b₁` are `1`, i.e. it exchanges
`|110⟩ = 6` and `|111⟩ = 7` and fixes everything else. -/

lemma toffoli_mulVec_basis (b₂ b₁ b₀ : Bool) :
    toffoli.mulVec (Pi.single (bitIdx b₂ b₁ b₀) (1 : ℂ))
      = Pi.single (bitIdx b₂ b₁ (xor b₀ (b₂ && b₁))) (1 : ℂ) := by
  funext i
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, toffoli_apply, toffoliPerm_bitIdx]
  by_cases h : i = bitIdx b₂ b₁ (xor b₀ (b₂ && b₁))
  · rw [if_pos h, h, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne h]

/-- **The Toffoli (CCNOT) matrix is a permutation matrix, hence unitary, and it is its
own inverse.** -/
