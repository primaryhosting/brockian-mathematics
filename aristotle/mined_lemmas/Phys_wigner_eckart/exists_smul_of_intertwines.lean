/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

open scoped TensorProduct

variable {G : Type*} [Group G]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A (complex) representation is *irreducible* if the space is nontrivial and the only
subspaces invariant under the group action are `⊥` and `⊤`. -/

theorem exists_smul_of_intertwines [FiniteDimensional ℂ V] (hρ : IsIrrep ρ) (hσ : IsIrrep σ)
    {S : V →ₗ[ℂ] W} (hS : Intertwines ρ σ S) (hS0 : S ≠ 0)
    {T : V →ₗ[ℂ] W} (hT : Intertwines ρ σ T) :
    ∃ c : ℂ, T = c • S := by
  haveI : Nontrivial V := hρ.1
  have hbij : Function.Bijective S := ⟨hS.injective hρ hS0, hS.surjective hσ hS0⟩
  let e : V ≃ₗ[ℂ] W := LinearEquiv.ofBijective S hbij
  have he : ∀ v : V, e v = S v := fun v => rfl
  have hesymm : ∀ (g : G) (w : W), e.symm (σ g w) = ρ g (e.symm w) := by
    intro g w
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he (ρ g (e.symm w)), hS g (e.symm w), ← he,
      LinearEquiv.apply_symm_apply]
  let f : Module.End ℂ V := (e.symm : W →ₗ[ℂ] V) ∘ₗ T
  have hf : ∀ (g : G) (v : V), f (ρ g v) = ρ g (f v) := by
    intro g v
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hT g v, hesymm g (T v)]
  obtain ⟨c, hc⟩ := f.exists_eigenvalue
  have hinv : ∀ (g : G) (v : V), v ∈ Module.End.eigenspace f c → ρ g v ∈
      Module.End.eigenspace f c := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hf g v, hv, map_smul]
  have htop : Module.End.eigenspace f c = ⊤ := by
    rcases hρ.2 _ hinv with h | h
    · exact absurd h hc
    · exact h
  refine ⟨c, ?_⟩
  ext v
  have hv : f v = c • v := by
    rw [← Module.End.mem_eigenspace_iff, htop]
    exact Submodule.mem_top
  have : T v = e (f v) := by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [this, hv, map_smul, he]
  simp

/-- There is a *universal* intertwiner `S` (unique up to scale) such that every intertwiner is a
scalar multiple of it: the space of intertwiners between irreducible representations is at most
one-dimensional. -/
