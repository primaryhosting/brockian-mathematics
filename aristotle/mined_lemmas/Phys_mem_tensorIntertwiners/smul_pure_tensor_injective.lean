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

theorem smul_pure_tensor_injective {f : U ⊗[ℂ] V →ₗ[ℂ] W} (hf : f ≠ 0) {r s : ℂ}
    (h : ∀ (u : U) (v : V), r • f (u ⊗ₜ[ℂ] v) = s • f (u ⊗ₜ[ℂ] v)) : r = s := by
  obtain ⟨u, v, huv⟩ := exists_pure_tensor_ne_zero hf
  have hsub : (r - s) • f (u ⊗ₜ[ℂ] v) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact h u v
  rcases smul_eq_zero.mp hsub with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' huv

/-- **Wigner–Eckart theorem** (algebraic core).

Let `ρU`, `ρV`, `ρW` be representations of a group `G` on complex vector spaces, and assume the
*multiplicity-one* condition: the space of intertwiners `U ⊗ V → W` has rank at most one (for
`SU(2)` this is the statement that an irreducible `W = V_{j'}` occurs at most once in
`V_k ⊗ V_j`).

Then, given a fixed nonzero intertwiner `CG` (the Clebsch–Gordan map), every intertwiner `T`
(a tensor operator) is a *unique* scalar multiple of it: there is a unique **reduced matrix
element** `r` with
`T (u ⊗ v) = r • CG (u ⊗ v)`
for all `u`, `v`. Taking components, all the dependence of the matrix elements of `T` on the
magnetic quantum numbers is carried by the Clebsch–Gordan coefficients. -/
