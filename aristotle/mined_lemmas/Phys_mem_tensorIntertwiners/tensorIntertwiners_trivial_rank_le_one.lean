import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

open TensorProduct

variable {G : Type*} [Group G] {U V W : Type*}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The space of intertwiners (equivariant linear maps) `U ⊗ V → W` for representations
`ρU`, `ρV`, `ρW` of a group `G`.

In the physical setting `U` carries the components `T^k_q` of a tensor operator of rank `k`,
`V` is the space of states `|j m⟩`, and `W` the space of states `|j' m'⟩`; an element of this
submodule is exactly an equivariant way of turning a component and a state into a state. -/

theorem tensorIntertwiners_trivial_rank_le_one (G : Type*) [Group G] :
    Module.rank ℂ
        (tensorIntertwiners (1 : Representation ℂ G ℂ) (1 : Representation ℂ G ℂ)
          (1 : Representation ℂ G ℂ)) ≤ 1 ∧
      ∃ CG ∈ tensorIntertwiners (1 : Representation ℂ G ℂ) (1 : Representation ℂ G ℂ)
          (1 : Representation ℂ G ℂ), CG ≠ (0 : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ) := by
  constructor
  · refine le_trans (Submodule.rank_le _) ?_
    simp [Module.rank_linearMap]
  · refine ⟨LinearMap.mul' ℂ ℂ, ?_, ?_⟩
    · intro g u v
      simp
    · intro h
      have h2 : (LinearMap.mul' ℂ ℂ : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = 0 := by
        rw [h]; simp
      simp at h2

end Phys

