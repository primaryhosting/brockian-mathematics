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
noncomputable def antisymState (𝕜 H : Type*) [Field 𝕜] [AddCommGroup H] [Module 𝕜 H] :
    H →ₗ[𝕜] H →ₗ[𝕜] H ⊗[𝕜] H :=
  TensorProduct.mk 𝕜 H H - (TensorProduct.mk 𝕜 H H).flip

@[simp] lemma antisymState_apply (u v : H) :
    antisymState 𝕜 H u v = u ⊗ₜ[𝕜] v - v ⊗ₜ[𝕜] u := rfl

/-- The two-fermion state is antisymmetric under exchange of the two particles. -/
theorem antisymState_swap (u v : H) :
    antisymState 𝕜 H v u = -antisymState 𝕜 H u v := by
  simp [neg_sub]

/-- **Pauli exclusion principle.**  A two-fermion antisymmetric state whose two
single-particle states coincide is the zero state. -/
theorem pauli_exclusion_antisym (u : H) : antisymState 𝕜 H u u = 0 := by
  simp

private lemma notMem_span_singleton_of_linearIndependent_pair {u v : H}
    (h : LinearIndependent 𝕜 ![u, v]) : u ∉ Submodule.span 𝕜 {v} := by
  have := h.notMem_span_image (s := {1}) (x := 0) (by simp)
  simpa [Set.image, Submodule.span_image] using this

private lemma linearIndependent_pair_swap {u v : H}
    (h : LinearIndependent 𝕜 ![u, v]) : LinearIndependent 𝕜 ![v, u] := by
  have := h.comp (Equiv.swap (0 : Fin 2) 1) (Equiv.injective _)
  convert this using 1
  ext i
  fin_cases i <;> simp

set_option maxRecDepth 40000 in
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
theorem pauli_exclusion_wedge (u : H) :
    (ExteriorAlgebra.ι 𝕜 u) * (ExteriorAlgebra.ι 𝕜 u) = 0 :=
  ExteriorAlgebra.ι_sq_zero u

/-- Pauli exclusion for Slater determinants of wavefunctions on a set of modes `ι`:
the two-particle wavefunction `Ψ i j = f i * g j - f j * g i` vanishes identically
when the two single-particle wavefunctions coincide. -/
theorem pauli_exclusion_slater {ι : Type*} (f g : ι → 𝕜) (hfg : f = g) (i j : ι) :
    f i * g j - f j * g i = 0 := by
  subst hfg; ring

end QPhys

#print axioms QPhys.pauli_exclusion_antisym
#print axioms QPhys.antisymState_ne_zero_of_linearIndependent
#print axioms QPhys.pauli_exclusion_wedge
#print axioms QPhys.pauli_exclusion_slater

