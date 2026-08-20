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

lemma toffoli_mul_self : toffoli * toffoli = 1 := by
  ext i j
  simp only [Matrix.mul_apply, toffoli_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (toffoliPerm j)]
  · by_cases h : i = j
    · subst h
      simp [toffoliPerm_involutive i]
    · have : ¬ i = toffoliPerm (toffoliPerm j) := by
        rwa [toffoliPerm_involutive j]
      simp [this, h]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Index of the computational basis state `|b₂ b₁ b₀⟩` of three qubits. -/
