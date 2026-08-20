/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Statement: Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

open TensorProduct

variable {G : Type*} [Monoid G]

/-- `f` intertwines the representations `ρ` and `σ`. -/

theorem intertwiner_eq_smul_fst
    (ρi : Representation ℂ G Vi) (ρf : Representation ℂ G Vf) (ρK : Representation ℂ G K)
    (hirr : IsIrred ρf)
    (e : Vi ≃ₗ[ℂ] Vf × K)
    (he : ∀ (g : G) (v : Vi), e (ρi g v) = (ρf g (e v).1, ρK g (e v).2))
    (hmult : ∀ f : K →ₗ[ℂ] Vf, Intertwines ρK ρf f → f = 0)
    (A : Vi →ₗ[ℂ] Vf) (hA : Intertwines ρi ρf A) :
    ∃ a : ℂ, ∀ v : Vi, A v = a • (e v).1 := by
  -- equivariance of `e.symm`
  have hesymm : ∀ (g : G) (p : Vf × K),
      e.symm (ρf g p.1, ρK g p.2) = ρi g (e.symm p) := by
    intro g p
    have := he g (e.symm p)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, LinearEquiv.symm_apply_apply]
  -- restriction to the first summand
  set A₁ : Vf →ₗ[ℂ] Vf :=
    A ∘ₗ (e.symm : Vf × K →ₗ[ℂ] Vi) ∘ₗ LinearMap.inl ℂ Vf K with hA₁
  set A₂ : K →ₗ[ℂ] Vf :=
    A ∘ₗ (e.symm : Vf × K →ₗ[ℂ] Vi) ∘ₗ LinearMap.inr ℂ Vf K with hA₂
  have hA₁eq : Intertwines ρf ρf A₁ := by
    intro g y
    simp only [hA₁, LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe]
    have h0 : (ρf g y, (0 : K)) = (ρf g (y, (0 : K)).1, ρK g (y, (0 : K)).2) := by
      simp
    rw [h0, hesymm g (y, (0 : K)), hA]
  have hA₂eq : Intertwines ρK ρf A₂ := by
    intro g z
    simp only [hA₂, LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe]
    have h0 : ((0 : Vf), ρK g z) = (ρf g ((0 : Vf), z).1, ρK g ((0 : Vf), z).2) := by
      simp
    rw [h0, hesymm g ((0 : Vf), z), hA]
  obtain ⟨a, ha⟩ := schur_scalar ρf hirr A₁ hA₁eq
  have hA₂zero : A₂ = 0 := hmult A₂ hA₂eq
  refine ⟨a, ?_⟩
  intro v
  have hsplit : v = e.symm ((e v).1, 0) + e.symm (0, (e v).2) := by
    rw [← map_add]
    have : (((e v).1, (0 : K)) + ((0 : Vf), (e v).2)) = e v := by
      ext <;> simp
    rw [this, LinearEquiv.symm_apply_apply]
  calc A v = A (e.symm ((e v).1, 0)) + A (e.symm (0, (e v).2)) := by
        rw [← map_add, ← hsplit]
    _ = A₁ ((e v).1) + A₂ ((e v).2) := by
        simp only [hA₁, hA₂, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
          LinearEquiv.coe_coe]
    _ = a • (e v).1 := by rw [ha, hA₂zero]; simp

/-- **Wigner–Eckart, abstract form.** In a multiplicity-free situation, any two intertwiners
from the coupled space `Vi` to the irreducible `Vf` are proportional: `T = r • C`, with `r`
(the *reduced matrix element*) uniquely determined. -/
