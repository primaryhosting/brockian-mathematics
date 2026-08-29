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

theorem wigner_eckart {ρU : Representation ℂ G U} {ρV : Representation ℂ G V}
    {ρW : Representation ℂ G W}
    (hmult : Module.rank ℂ (tensorIntertwiners ρU ρV ρW) ≤ 1)
    (T CG : U ⊗[ℂ] V →ₗ[ℂ] W)
    (hT : T ∈ tensorIntertwiners ρU ρV ρW) (hCG : CG ∈ tensorIntertwiners ρU ρV ρW)
    (hCG0 : CG ≠ 0) :
    ∃! r : ℂ, ∀ (u : U) (v : V), T (u ⊗ₜ[ℂ] v) = r • CG (u ⊗ₜ[ℂ] v) := by
  obtain ⟨f₀, hf₀⟩ := rank_le_one_iff.mp hmult
  obtain ⟨a, ha⟩ := hf₀ ⟨CG, hCG⟩
  obtain ⟨b, hb⟩ := hf₀ ⟨T, hT⟩
  have haCG : a • (f₀ : U ⊗[ℂ] V →ₗ[ℂ] W) = CG := congrArg Subtype.val ha
  have hbT : b • (f₀ : U ⊗[ℂ] V →ₗ[ℂ] W) = T := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hCG0 (by simpa using haCG.symm)
  have hTCG : T = (b / a) • CG := by
    rw [← haCG, ← hbT, smul_smul, div_mul_cancel₀ _ ha0]
  refine ⟨b / a, fun u v => by rw [hTCG]; simp, fun y hy => ?_⟩
  refine smul_pure_tensor_injective hCG0 (fun u v => ?_)
  rw [← hy u v, hTCG]
  simp

/-- The Wigner–Eckart theorem in the form used in physics: with respect to any families of
"tensor operator components" `e q`, "initial states" `f m` and "final-state functionals" `bra m'`,
the matrix elements of an equivariant tensor operator `T` factor as a single reduced matrix
element `r` times the Clebsch–Gordan coefficients `bra m' (CG (e q ⊗ f m))`. -/
