/-
/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the mandated header above is kept as a
-- plain comment and repeated as the module docstring below.)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

section Defs

variable {n m : Type*}

/-- The matrix `n × m` representation of a vector `ψ` of the tensor product `H ⊗ K`,
where `H` has orthonormal basis indexed by `n` and `K` has orthonormal basis indexed by `m`. -/

theorem exists_isometry_comp_of_norm_eq {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (f g : E →ₗ[ℂ] F) (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ u : F →ₗᵢ[ℂ] F, ∀ x, u (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hx0 : f x = 0 := LinearMap.mem_ker.mp hx
    have : ‖g x‖ = 0 := by rw [← h x, hx0, norm_zero]
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp this)
  set q : (E ⧸ LinearMap.ker f) →ₗ[ℂ] F := (LinearMap.ker f).liftQ g hker with hq
  set e : (E ⧸ LinearMap.ker f) ≃ₗ[ℂ] (LinearMap.range f) := f.quotKerEquivRange with he
  have hsymm : ∀ x : E, e.symm ⟨f x, LinearMap.mem_range_self f x⟩
      = Submodule.Quotient.mk x := by
    intro x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he]
    exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f x).symm
  set L₀ : (LinearMap.range f) →ₗ[ℂ] F := q ∘ₗ (e.symm : (LinearMap.range f) →ₗ[ℂ] _) with hL₀
  have hval : ∀ x : E, L₀ ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    simp only [hL₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hsymm x, hq]
    exact (LinearMap.ker f).liftQ_apply g x
  have hnorm : ∀ y : (LinearMap.range f), ‖L₀ y‖ = ‖(y : F)‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hval x, ← h x]
  refine ⟨(⟨L₀, hnorm⟩ : (LinearMap.range f) →ₗᵢ[ℂ] F).extend, fun x => ?_⟩
  rw [(⟨L₀, hnorm⟩ : (LinearMap.range f) →ₗᵢ[ℂ] F).extend_apply
      ⟨f x, LinearMap.mem_range_self f x⟩]
  exact hval x

/-- A linear isometry of `EuclideanSpace ℂ m` is given by multiplication by a unitary matrix. -/
