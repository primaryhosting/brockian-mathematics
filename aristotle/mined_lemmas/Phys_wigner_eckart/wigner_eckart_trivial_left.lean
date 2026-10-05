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
open scoped TensorProduct

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

variable {G : Type*} [Monoid G]

/-- A linear map `f : V → U` *intertwines* the representations `ρ` (on `V`) and `σ` (on `U`)
if it commutes with the group action. -/

theorem wigner_eckart_trivial_left {U : Type*} [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (σ : Representation ℂ G U) (hσ : IsIrrep σ)
    (T : (ℂ ⊗[ℂ] U) →ₗ[ℂ] U) (hT : Intertwines ((1 : Representation ℂ G ℂ).tprod σ) σ T) :
    ∃ r : ℂ, ∀ (L : U →ₗ[ℂ] ℂ) (a : ℂ) (u : U),
      L (T (a ⊗ₜ[ℂ] u)) = r * L ((TensorProduct.lid ℂ U) (a ⊗ₜ[ℂ] u)) := by
  haveI := hσ.nontrivial
  have hKinv : ∀ (g : G), ∀ x ∈ (⊥ : Submodule ℂ (ℂ ⊗[ℂ] U)),
      ((1 : Representation ℂ G ℂ).tprod σ) g x ∈ (⊥ : Submodule ℂ (ℂ ⊗[ℂ] U)) := by
    intro g x hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]
  have hC0 : ((TensorProduct.lid ℂ U).toLinearMap) ≠ 0 := by
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    intro h
    apply hu
    have := LinearMap.congr_fun h ((1 : ℂ) ⊗ₜ[ℂ] u)
    simpa using this
  obtain ⟨r, hr⟩ := wigner_eckart (1 : Representation ℂ G ℂ) σ σ hσ ⊥ hKinv
    (by
      intro f _
      ext x
      have hx : x = 0 := Subtype.ext (Submodule.mem_bot ℂ |>.1 x.2)
      rw [hx, map_zero]
      simp)
    ((TensorProduct.lid ℂ U).symm.toLinearMap)
    (by
      intro g u
      simp)
    (by
      intro x
      exact ⟨(TensorProduct.lid ℂ U) x, 0, Submodule.zero_mem _, by simp⟩)
    ((TensorProduct.lid ℂ U).toLinearMap) T
    (by
      intro g x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a u => simp
      | add x y hx hy => simp only [map_add, hx, hy])
    hT hC0
  exact ⟨r, fun L a u => hr L a u⟩

end Phys

