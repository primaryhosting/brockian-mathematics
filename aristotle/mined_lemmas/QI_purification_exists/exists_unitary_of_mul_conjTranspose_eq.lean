/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

open scoped MatrixOrder ComplexOrder Kronecker InnerProductSpace
open Matrix

namespace QI

variable {n m : ℕ}

/-- The coefficient matrix of a vector `psi` of the tensor product `ℂ^n ⊗ ℂ^m`, whose
coordinates are indexed by `Fin n × Fin m`. -/

theorem exists_unitary_of_mul_conjTranspose_eq (A B : Matrix (Fin n) (Fin m) ℂ)
    (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix (Fin m) (Fin m) ℂ, U ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ B = A * U := by
  classical
  set f : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin Aᴴ with hf
  set g : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin Bᴴ with hg
  -- The Gram matrix computes the inner products of the images.
  have hgram : ∀ (C : Matrix (Fin n) (Fin m) ℂ) (x y : EuclideanSpace ℂ (Fin n)),
      ⟪Matrix.toEuclideanLin Cᴴ x, Matrix.toEuclideanLin Cᴴ y⟫_ℂ
        = ⟪x, Matrix.toEuclideanLin (C * Cᴴ) y⟫_ℂ := by
    intro C x y
    rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_left]
    rfl
  have hnorm : ∀ x, ‖f x‖ = ‖g x‖ := by
    intro x
    have hx : ⟪f x, f x⟫_ℂ = ⟪g x, g x⟫_ℂ := by rw [hf, hg, hgram, hgram, h]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hx]
  -- Hence `f x ↦ g x` is a well-defined isometry from the range of `f`.
  have hkerle : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hfx : f x = 0 := hx
    have hgx : ‖g x‖ = 0 := by rw [← hnorm, hfx, norm_zero]
    simpa [LinearMap.mem_ker] using norm_eq_zero.mp hgx
  set L0 : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    ((LinearMap.ker f).liftQ g hkerle) ∘ₗ
      (f.quotKerEquivRange.symm : LinearMap.range f →ₗ[ℂ] _) with hL0def
  have hL0 : ∀ x, L0 ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    rw [hL0def]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
      Submodule.liftQ_apply]
  have hL0norm : ∀ y : LinearMap.range f, ‖L0 y‖ = ‖y‖ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    rw [hL0, ← hnorm]
    rfl
  set L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
    { toLinearMap := L0, norm_map' := hL0norm } with hLdef
  -- Extend it to an isometry of the whole ancilla space.
  set W := L.extend with hWdef
  have hW : ∀ x, W (f x) = g x := by
    intro x
    have hx := L.extend_apply ⟨f x, LinearMap.mem_range_self f x⟩
    rw [hWdef]
    rw [show ((⟨f x, LinearMap.mem_range_self f x⟩ : LinearMap.range f) :
      EuclideanSpace ℂ (Fin m)) = f x from rfl] at hx
    rw [hx, hLdef]
    exact hL0 x
  -- The matrix of that isometry is unitary and conjugates `Aᴴ` into `Bᴴ`.
  set U0 : Matrix (Fin m) (Fin m) ℂ := Matrix.toEuclideanLin.symm W.toLinearMap with hU0def
  have hU0 : Matrix.toEuclideanLin U0 = W.toLinearMap := by
    rw [hU0def, LinearEquiv.apply_symm_apply]
  have hU0mem : U0 ∈ Matrix.unitaryGroup (Fin m) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_one]
    have hstar : (star U0 : Matrix (Fin m) (Fin m) ℂ) = U0ᴴ := rfl
    rw [hstar, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hU0]
    refine LinearMap.ext fun x => ?_
    apply ext_inner_left ℂ
    intro y
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, LinearMap.id_apply]
    exact W.inner_map_map y x
  have hmat : U0 * Aᴴ = Bᴴ := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hU0]
    exact LinearMap.ext fun x => hW x
  refine ⟨U0ᴴ, Unitary.star_mem hU0mem, ?_⟩
  have hcT := congrArg Matrix.conjTranspose hmat
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at hcT
  exact hcT.symm

/-- **Purification.**  Every mixed state `rho` on `ℂ^n` (a positive semidefinite matrix of
trace one) admits a purification: a unit vector `psi` of `ℂ^n ⊗ ℂ^n` whose reduced state on
the first factor is `rho`.  Moreover a purification is unique up to a unitary acting on the
ancilla: any two vectors of `ℂ^n ⊗ ℂ^m` whose reduced state is `rho` are related by
`1 ⊗ U` for some unitary `U` of the ancilla `ℂ^m`. -/
