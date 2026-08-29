import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

section Defs

variable {n m : Type*}

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ` of a composite system whose
product basis is indexed by `n × m`. -/

lemma exists_linearIsometry_comp [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (f g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m) (hnorm : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ W : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m, ∀ x, W (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at *
    have h2 := hnorm x
    rw [hx] at h2
    exact norm_eq_zero.mp (by simpa using h2.symm)
  set L₀ : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ m :=
    ((LinearMap.ker f).liftQ g hker).comp (f.quotKerEquivRange.symm : (LinearMap.range f) →ₗ[ℂ] _)
    with hL₀def
  have hL₀ : ∀ x : EuclideanSpace ℂ n, L₀ ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    have h1 : f.quotKerEquivRange (Submodule.Quotient.mk x) = ⟨f x, ⟨x, rfl⟩⟩ := rfl
    simp only [hL₀def, LinearMap.comp_apply, LinearEquiv.coe_coe, ← h1,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  set L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ m :=
    { toLinearMap := L₀
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        rw [hL₀ x]
        exact (hnorm x).symm } with hLdef
  refine ⟨L.extend, fun x => ?_⟩
  have hx := L.extend_apply ⟨f x, ⟨x, rfl⟩⟩
  simpa [hLdef, hL₀ x] using hx

/-- Every linear isometry of `EuclideanSpace ℂ m` is given by a unitary matrix. -/
