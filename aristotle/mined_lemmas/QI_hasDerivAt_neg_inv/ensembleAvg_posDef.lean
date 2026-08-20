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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem ensembleAvg_posDef (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hρ : ∀ x, (ρ x).PosDef) : (ensembleAvg p ρ).PosDef := by
  classical
  obtain ⟨x₀, -, hx₀⟩ : ∃ x₀ ∈ Finset.univ, 0 < p x₀ := by
    by_contra h
    push_neg at h
    have hle : ∑ x, p x ≤ 0 := Finset.sum_nonpos fun x hx => h x hx
    rw [hp1] at hle
    norm_num at hle
  rw [ensembleAvg, ← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)]
  refine Matrix.PosDef.add_posSemidef ((hρ x₀).smul ?_) ?_
  · exact_mod_cast hx₀
  · exact posSemidef_sum _ _ fun x _ => (hρ x).posSemidef.smul (by exact_mod_cast hp0 x)

