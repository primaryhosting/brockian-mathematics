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

namespace QPhys

open TensorProduct

variable {𝕜 H : Type*} [Field 𝕜] [AddCommGroup H] [Module 𝕜 H]

/-- The antisymmetrized (fermionic) two-particle state built from two single-particle
states `u` and `v`, living in `H ⊗ H`:  `antisymState u v = u ⊗ v - v ⊗ u`. -/

theorem antisymState_ne_zero_of_linearIndependent {u v : H}
    (h : LinearIndependent 𝕜 ![u, v]) : antisymState 𝕜 H u v ≠ 0 := by
  -- Extract functionals `f`, `g` dual to `u`, `v`.
  obtain ⟨f, hf⟩ : ∃ f : H →ₗ[𝕜] 𝕜, f u = 1 ∧ f v = 0 :=
    exists_dual_pair (u := u) (v := v) (notMem_span_singleton_of_linearIndependent_pair h)
  obtain ⟨g, hg⟩ : ∃ g : H →ₗ[𝕜] 𝕜, g v = 1 ∧ g u = 0 :=
    exists_dual_pair (u := v) (v := u)
      (notMem_span_singleton_of_linearIndependent_pair (linearIndependent_pair_swap h))
  intro hzero
  have := congrArg (TensorProduct.lift ((LinearMap.mul 𝕜 𝕜).compl₁₂ f g)) hzero
  simp [hf.1, hf.2, hg.1, hg.2] at this


/-- Pauli exclusion in the exterior algebra picture: the fermionic (wedge) product of a
single-particle state with itself vanishes. -/
