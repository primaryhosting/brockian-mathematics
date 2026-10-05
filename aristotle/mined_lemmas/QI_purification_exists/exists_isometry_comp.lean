import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexConjugate MatrixOrder ComplexOrder

namespace QI

/-! ### Basic definitions -/

section Defs

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- A density matrix (mixed state): a positive semidefinite matrix of unit trace. -/

theorem exists_isometry_comp (f g : E →ₗ[ℂ] F) (hn : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ L : F →ₗᵢ[ℂ] F, ∀ x, L (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have := hn x
    rw [LinearMap.mem_ker.1 hx, norm_zero] at this
    exact LinearMap.mem_ker.2 (norm_eq_zero.1 this.symm)
  set g' := (LinearMap.ker f).liftQ g hker with hg'
  set q := f.quotKerEquivRange with hq
  set φ₀ : ↥(LinearMap.range f) →ₗ[ℂ] F := g'.comp q.symm.toLinearMap with hφ₀def
  have key : ∀ x : E, φ₀ ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    have hqx : q (Submodule.Quotient.mk x) = ⟨f x, ⟨x, rfl⟩⟩ :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f x)
    have h2 : q.symm ⟨f x, ⟨x, rfl⟩⟩ = Submodule.Quotient.mk x := by
      rw [← hqx, LinearEquiv.symm_apply_apply]
    simp [hφ₀def, h2, hg']
  have hnorm : ∀ y : ↥(LinearMap.range f), ‖φ₀ y‖ = ‖y‖ := by
    rintro ⟨y, x, rfl⟩
    rw [key x]
    simpa using (hn x).symm
  refine ⟨(⟨φ₀, hnorm⟩ : ↥(LinearMap.range f) →ₗᵢ[ℂ] F).extend, fun x => ?_⟩
  have := LinearIsometry.extend_apply (⟨φ₀, hnorm⟩ : ↥(LinearMap.range f) →ₗᵢ[ℂ] F)
      ⟨f x, ⟨x, rfl⟩⟩
  simpa [key x] using this

end Isom

/-! ### The unitary freedom in decompositions `A Aᴴ = B Bᴴ` -/

section Freedom

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- The matrix of a linear isometry of `EuclideanSpace ℂ K`. -/
