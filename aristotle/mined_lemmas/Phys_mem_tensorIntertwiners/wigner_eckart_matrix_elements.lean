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

theorem wigner_eckart_matrix_elements {ρU : Representation ℂ G U} {ρV : Representation ℂ G V}
    {ρW : Representation ℂ G W}
    (hmult : Module.rank ℂ (tensorIntertwiners ρU ρV ρW) ≤ 1)
    (T CG : U ⊗[ℂ] V →ₗ[ℂ] W)
    (hT : T ∈ tensorIntertwiners ρU ρV ρW) (hCG : CG ∈ tensorIntertwiners ρU ρV ρW)
    (hCG0 : CG ≠ 0)
    {Q M M' : Type*} (e : Q → U) (f : M → V) (bra : M' → (W →ₗ[ℂ] ℂ)) :
    ∃ r : ℂ, ∀ (m' : M') (q : Q) (m : M),
      bra m' (T (e q ⊗ₜ[ℂ] f m)) = r * bra m' (CG (e q ⊗ₜ[ℂ] f m)) := by
  obtain ⟨r, hr, -⟩ := wigner_eckart hmult T CG hT hCG hCG0
  refine ⟨r, fun m' q m => ?_⟩
  rw [hr (e q) (f m)]
  simp

/-- The multiplicity-one hypothesis of `Phys.wigner_eckart` is satisfiable, together with the
existence of a nonzero Clebsch-Gordan intertwiner: for the trivial representations on `ℂ` the
intertwiner space has rank at most one and contains the (nonzero) multiplication map. -/
