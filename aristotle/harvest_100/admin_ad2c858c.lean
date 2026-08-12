/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A mixed state on `ℂ^n` is modelled by a density matrix `rho : Matrix n n ℂ`, i.e. a positive
semidefinite matrix of unit trace.  A vector of the composite system `ℂ^n ⊗ ℂ^m` is modelled by
a matrix `M : Matrix n m ℂ` (its matrix of coefficients in the product basis), the squared
Hilbert–Schmidt norm `∑ i j, ‖M i j‖ ^ 2` being its squared norm as a vector, and its partial
trace over the ancilla `ℂ^m` being `M * Mᴴ`.

The main result `QI.purification_exists` states that every mixed state `rho` has a purification
by a unit vector of `ℂ^n ⊗ ℂ^n`, and that any two purifications with the same ancilla differ by
a unitary acting on the ancilla only.
-/

open scoped BigOperators
open scoped ComplexConjugate
open scoped ComplexOrder
open scoped MatrixOrder

namespace QI

open Matrix

/-- A *mixed state* (density matrix) on the finite-dimensional Hilbert space `ℂ^n`:
a positive semidefinite matrix of unit trace. -/
def IsMixedState {n : Type*} [Fintype n] (rho : Matrix n n ℂ) : Prop :=
  rho.PosSemidef ∧ rho.trace = 1

/-- `M` is a *purification* of `rho` with ancilla index type `m`.

A vector `ψ ∈ ℂ^n ⊗ ℂ^m` is the same thing as a matrix `M : Matrix n m ℂ`
(via `ψ = ∑ i j, M i j • (eᵢ ⊗ eⱼ)`), and the reduced density matrix of `ψ`
on the first factor (the partial trace over the ancilla) is `M * Mᴴ`.
So `M` purifies `rho` exactly when `M * Mᴴ = rho`. -/
def IsPurification {n m : Type*} [Fintype n] [Fintype m]
    (rho : Matrix n n ℂ) (M : Matrix n m ℂ) : Prop :=
  M * Mᴴ = rho

section Aux

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq m] in
/-- The inner products between the images of the map `x ↦ Mᴴ x` are determined by `M * Mᴴ`. -/
lemma inner_toEuclideanLin_conjTranspose (M : Matrix n m ℂ) (x y : EuclideanSpace ℂ n) :
    inner ℂ (Matrix.toEuclideanLin Mᴴ x) (Matrix.toEuclideanLin Mᴴ y)
      = inner ℂ x (Matrix.toEuclideanLin (M * Mᴴ) y) := by
  have key : (star (Mᴴ *ᵥ x.ofLp)) ⬝ᵥ (Mᴴ *ᵥ y.ofLp) = (star x.ofLp) ⬝ᵥ ((M * Mᴴ) *ᵥ y.ofLp) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec,
      ← Matrix.dotProduct_mulVec]
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  have h1 : ((toEuclideanLin Mᴴ) y).ofLp = Mᴴ *ᵥ y.ofLp := rfl
  have h2 : ((toEuclideanLin Mᴴ) x).ofLp = Mᴴ *ᵥ x.ofLp := rfl
  have h3 : ((toEuclideanLin (M * Mᴴ)) y).ofLp = (M * Mᴴ) *ᵥ y.ofLp := rfl
  rw [h1, h2, h3, dotProduct_comm, key, dotProduct_comm]

/-- A linear map between finite-dimensional inner product spaces can be transported onto another
one with the same norms by a global linear isometry of the target. -/
lemma exists_linearIsometry_comp_eq {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (f g : E →ₗ[ℂ] V) (hnorm : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ U : V →ₗᵢ[ℂ] V, ∀ x, U (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have h0 : ‖g x‖ = 0 := by rw [← hnorm x, LinearMap.mem_ker.mp hx, norm_zero]
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp h0)
  let L₀ : (E ⧸ LinearMap.ker f) →ₗ[ℂ] V := (LinearMap.ker f).liftQ g hker
  let Lmap : (LinearMap.range f) →ₗ[ℂ] V :=
    L₀ ∘ₗ (f.quotKerEquivRange.symm : LinearMap.range f →ₗ[ℂ] (E ⧸ LinearMap.ker f))
  have hLmap : ∀ x : E, Lmap ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    show L₀ (f.quotKerEquivRange.symm ⟨f x, ⟨x, rfl⟩⟩) = g x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simp [L₀]
  let L : (LinearMap.range f) →ₗᵢ[ℂ] V := ⟨Lmap, by
    intro s
    obtain ⟨x, hx⟩ := s.2
    have hs : s = ⟨f x, ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
    rw [hs, hLmap x]
    show ‖g x‖ = ‖(⟨f x, ⟨x, rfl⟩⟩ : LinearMap.range f)‖
    rw [← hnorm x]
    rfl⟩
  refine ⟨L.extend, fun x => ?_⟩
  have h1 := L.extend_apply ⟨f x, ⟨x, rfl⟩⟩
  have h2 : (L ⟨f x, ⟨x, rfl⟩⟩ : V) = g x := hLmap x
  rw [h2] at h1
  exact h1

/-- The matrix of a linear isometry of `ℂ^m` in the standard (orthonormal) basis is unitary. -/
lemma toMatrix_linearIsometry_mem_unitaryGroup
    (U : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m) :
    (LinearMap.toMatrix (EuclideanSpace.basisFun m ℂ).toBasis (EuclideanSpace.basisFun m ℂ).toBasis
      U.toLinearMap) ∈ Matrix.unitaryGroup m ℂ := by
  set b := EuclideanSpace.basisFun m ℂ with hb
  set W := LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap with hW
  have hentry : ∀ i j, W i j = inner ℂ (b i) (U (b j)) := by
    intro i j
    rw [hW, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
    rfl
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  rw [Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hentry, Matrix.one_apply]
  have hstep : ∀ k, star (inner ℂ (b k) (U (b i))) * inner ℂ (b k) (U (b j))
      = inner ℂ (U (b i)) (b k) * inner ℂ (b k) (U (b j)) := by
    intro k; rw [← inner_conj_symm (U (b i)) (b k)]; rfl
  simp only [hstep]
  rw [OrthonormalBasis.sum_inner_mul_inner, LinearIsometry.inner_map_map,
    orthonormal_iff_ite.mp b.orthonormal i j]

/-- **Unitary freedom.** If two matrices with the same index types satisfy `M * Mᴴ = N * Nᴴ`,
then they differ by a unitary acting on the column index: `N = M * W`. -/
theorem exists_unitary_of_mul_conjTranspose_eq (M N : Matrix n m ℂ) (h : M * Mᴴ = N * Nᴴ) :
    ∃ W : Matrix m m ℂ, W ∈ Matrix.unitaryGroup m ℂ ∧ N = M * W := by
  set f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m := Matrix.toEuclideanLin Mᴴ with hf
  set g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m := Matrix.toEuclideanLin Nᴴ with hg
  -- the two maps have the same norms, since `M Mᴴ = N Nᴴ`
  have hnorm : ∀ x, ‖f x‖ = ‖g x‖ := by
    intro x
    have h1 := inner_toEuclideanLin_conjTranspose M x x
    have h2 := inner_toEuclideanLin_conjTranspose N x x
    rw [h] at h1
    have hinner : (inner ℂ (f x) (f x) : ℂ) = inner ℂ (g x) (g x) := by rw [hf, hg, h1, h2]
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hinner]
  -- so they are intertwined by a linear isometry of the ancilla space
  obtain ⟨U, hU⟩ := exists_linearIsometry_comp_eq f g hnorm
  set b := EuclideanSpace.basisFun m ℂ with hb
  refine ⟨(LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap)ᴴ, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (toMatrix_linearIsometry_mem_unitaryGroup U)
  · set W := LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap with hW
    have hWlin : Matrix.toEuclideanLin W = U.toLinearMap := by
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, hW]
      exact Matrix.toLin_toMatrix _ _ _
    have hmul : Matrix.toEuclideanLin (W * Mᴴ)
        = (Matrix.toEuclideanLin W).comp (Matrix.toEuclideanLin Mᴴ) := by
      ext x i
      simp [Matrix.mulVec_mulVec]
    have heq : W * Mᴴ = Nᴴ := by
      apply Matrix.toEuclideanLin.injective
      rw [hmul, hWlin]
      ext x i
      exact congrArg (fun v : EuclideanSpace ℂ m => v.ofLp i) (hU x)
    have := congrArg Matrix.conjTranspose heq
    simpa [Matrix.conjTranspose_mul] using this.symm

omit [DecidableEq n] [DecidableEq m] in
/-- The trace of `M * Mᴴ` is the squared Hilbert–Schmidt (Frobenius) norm of `M`. -/
lemma trace_mul_conjTranspose (M : Matrix n m ℂ) :
    (M * Mᴴ).trace = ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Aux

/-- **Purification of mixed states.**

For every mixed state `rho` on `ℂ^n` (a positive semidefinite matrix of unit trace):

* **Existence**: there is a purification `M` of `rho` with ancilla space `ℂ^n`, i.e. a vector
  `M` of `ℂ^n ⊗ ℂ^n` which is a unit vector (`∑ i j, ‖M i j‖ ^ 2 = 1`) and whose partial trace
  over the ancilla, `M * Mᴴ`, is `rho`.
* **Uniqueness up to an isometry on the ancilla**: any two purifications `M`, `N` of `rho`
  with the same ancilla index type `m` differ by a unitary `W` acting on the ancilla alone:
  `N = M * W`. -/
theorem purification_exists {n : Type} [Fintype n] [DecidableEq n]
    (rho : Matrix n n ℂ) (h : IsMixedState rho) :
    (∃ M : Matrix n n ℂ, IsPurification rho M ∧ ∑ i, ∑ j, ‖M i j‖ ^ 2 = 1) ∧
      ∀ (m : Type) [Fintype m] [DecidableEq m] (M N : Matrix n m ℂ),
        IsPurification rho M → IsPurification rho N →
          ∃ W : Matrix m m ℂ, W ∈ Matrix.unitaryGroup m ℂ ∧ N = M * W := by
  obtain ⟨hpsd, htr⟩ := h
  constructor
  · -- the positive semidefinite square root of `rho` is a purification
    refine ⟨CFC.sqrt rho, ?_, ?_⟩
    · have h2 : (CFC.sqrt rho).PosSemidef := (CFC.sqrt_nonneg rho).posSemidef
      show CFC.sqrt rho * (CFC.sqrt rho)ᴴ = rho
      rw [h2.isHermitian.eq]
      exact CFC.sqrt_mul_sqrt_self rho hpsd.nonneg
    · have h2 : (CFC.sqrt rho).PosSemidef := (CFC.sqrt_nonneg rho).posSemidef
      have hpur : CFC.sqrt rho * (CFC.sqrt rho)ᴴ = rho := by
        rw [h2.isHermitian.eq]; exact CFC.sqrt_mul_sqrt_self rho hpsd.nonneg
      have := trace_mul_conjTranspose (CFC.sqrt rho)
      rw [hpur, htr] at this
      exact_mod_cast this.symm
  · intro m _ _ M N hM hN
    exact exists_unitary_of_mul_conjTranspose_eq M N (by rw [hM, hN])

/-- Sanity check that the hypothesis of `purification_exists` is satisfiable: the maximally
mixed state of a qubit is a mixed state. -/
example : IsMixedState ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨Matrix.PosSemidef.smul Matrix.PosSemidef.one ?_, by simp [Matrix.trace_smul]⟩
  rw [RCLike.nonneg_iff]
  norm_num

end QI

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

