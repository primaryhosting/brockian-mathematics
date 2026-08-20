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

private lemma exists_dual_pair {u v : H} (h : u ∉ Submodule.span 𝕜 {v}) :
    ∃ f : H →ₗ[𝕜] 𝕜, f u = 1 ∧ f v = 0 := by
  obtain ⟨f, hf, hf'⟩ := (Submodule.span 𝕜 {v}).exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨(f u)⁻¹ • f, by simp [inv_mul_cancel₀ hf], ?_⟩
  have hv : f v = 0 := by
    have hmem : f v ∈ Submodule.map f (Submodule.span 𝕜 {v}) :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self v)
    rw [hf'] at hmem
    exact (Submodule.mem_bot 𝕜).mp hmem
  simp [hv]

/-- Conversely, the antisymmetrized state of two linearly independent single-particle
states is nonzero: the vanishing in `pauli_exclusion_antisym` is really due to the
coincidence of the states. -/
