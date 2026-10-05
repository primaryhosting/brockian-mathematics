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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Matrix

universe u v

/-! ## Linear-algebraic preliminaries -/

/-- The inner product of two images under a matrix, expressed through `Mᴴ * M`. -/

theorem exists_isometry_of_inner_eq {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (a b : V →ₗ[ℂ] W)
    (hinner : ∀ x y : V, inner ℂ (a x) (a y) = inner ℂ (b x) (b y)) :
    ∃ U : W →ₗᵢ[ℂ] W, ∀ x : V, U (a x) = b x := by
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have hxx := hinner x x
    rw [hx] at hxx
    simpa [inner_self_eq_zero] using hxx.symm
  let bq := (LinearMap.ker a).liftQ b hker
  let e := LinearMap.quotKerEquivRange a
  let g : ↥(LinearMap.range a) →ₗ[ℂ] W := bq ∘ₗ (e.symm : ↥(LinearMap.range a) →ₗ[ℂ] _)
  have hgap : ∀ x : V, g ⟨a x, LinearMap.mem_range_self a x⟩ = b x := by
    intro x
    have h1 : e.symm ⟨a x, LinearMap.mem_range_self a x⟩ = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      simp [e, LinearMap.quotKerEquivRange_apply_mk]
    show bq (e.symm _) = b x
    rw [h1]
    simp [bq]
  have hiso : ∀ w z : ↥(LinearMap.range a), inner ℂ (g w) (g z) = inner ℂ w z := by
    rintro ⟨w, x, rfl⟩ ⟨z, y, rfl⟩
    rw [hgap x, hgap y, ← hinner x y]
    rfl
  refine ⟨(LinearMap.isometryOfInner g hiso).extend, fun x => ?_⟩
  have hext := (LinearMap.isometryOfInner g hiso).extend_apply
    ⟨a x, LinearMap.mem_range_self a x⟩
  simpa [hgap x] using hext

/-- If `A * Aᴴ = B * Bᴴ` then `B = A * U` for some unitary matrix `U`. -/
