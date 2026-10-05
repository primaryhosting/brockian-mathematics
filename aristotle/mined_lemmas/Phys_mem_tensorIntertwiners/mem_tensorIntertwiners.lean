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

theorem mem_tensorIntertwiners {ρU : Representation ℂ G U} {ρV : Representation ℂ G V}
    {ρW : Representation ℂ G W} {f : U ⊗[ℂ] V →ₗ[ℂ] W} :
    f ∈ tensorIntertwiners ρU ρV ρW ↔
      ∀ (g : G) (u : U) (v : V), f (ρU g u ⊗ₜ[ℂ] ρV g v) = ρW g (f (u ⊗ₜ[ℂ] v)) :=
  Iff.rfl

/-- A nonzero map is nonzero on some pure tensor. -/
