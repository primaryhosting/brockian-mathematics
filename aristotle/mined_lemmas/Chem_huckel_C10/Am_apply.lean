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

namespace Chem

attribute [local instance] Fin.instCommRing

/-! ### A primitive 10-th root of unity -/

/-- The primitive 10-th root of unity `exp (2πi/10)`. -/

lemma Am_apply (j k : Fin 10) :
    Am j k = (if k = j - 1 then (1 : ℂ) else 0) + (if k = j + 1 then (1 : ℂ) else 0) := by
  have hadj : (SimpleGraph.cycleGraph 10).Adj j k ↔ (k = j - 1 ∨ k = j + 1) := by
    rw [SimpleGraph.cycleGraph_adj]
    constructor
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
    · rintro (rfl | rfl)
      · left; ring
      · right; ring
  have hne : (j - 1 : Fin 10) ≠ j + 1 := by
    intro h
    have h2 : (2 : Fin 10) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  simp only [Am, SimpleGraph.adjMatrix_apply, hadj]
  by_cases h1 : k = j - 1
  · simp [h1, hne]
  · by_cases h2 : k = j + 1 <;> simp [h1, h2, Ne.symm hne]

