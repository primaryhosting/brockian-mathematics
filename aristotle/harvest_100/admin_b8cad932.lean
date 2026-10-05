/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped ComplexOrder MatrixOrder

namespace QI

open Matrix

/-- A state `ψ` of the composite system `system ⊗ ancilla`, written as a matrix whose rows are
indexed by the system and whose columns are indexed by the ancilla, is a *purification* of the
mixed state `ρ` if tracing out the ancilla returns `ρ`. -/
def IsPurification {n m : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) (ψ : Matrix (Fin n) (Fin m) ℂ) :
    Prop :=
  ∀ i j, ρ i j = ∑ k, ψ i k * star (ψ j k)

/-- Tracing out the ancilla is the map `ψ ↦ ψ * ψᴴ`. -/
theorem isPurification_iff {n m : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (ψ : Matrix (Fin n) (Fin m) ℂ) : IsPurification ρ ψ ↔ ψ * ψᴴ = ρ := by
  constructor
  · intro h
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, h i j]
  · intro h i j
    rw [← h]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Two matrices with the same Gram matrix `Xᴴ * X` differ by a unitary acting on the left. -/
theorem exists_unitary_mul_eq {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℂ)
    (h : Xᴴ * X = Yᴴ * Y) :
    ∃ W ∈ Matrix.unitaryGroup (Fin m) ℂ, W * X = Y := by
  classical
  -- Multiplication of matrices corresponds to composition of the associated linear maps.
  have hmulcomp : ∀ {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin q) (Fin r) ℂ)
      (v : EuclideanSpace ℂ (Fin r)), Matrix.toEuclideanLin (A * B) v
        = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
    intro p q r A B v
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  -- The Gram matrix computes inner products of images.
  have key : ∀ (Z : Matrix (Fin m) (Fin n) ℂ) (v w : EuclideanSpace ℂ (Fin n)),
      inner ℂ (Matrix.toEuclideanLin Z v) (Matrix.toEuclideanLin Z w)
        = inner ℂ v (Matrix.toEuclideanLin (Zᴴ * Z) w) := by
    intro Z v w
    rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin Z) v (Matrix.toEuclideanLin Z w),
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hmulcomp]
  set fX : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin X with hfX
  set fY : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin Y with hfY
  have hinner : ∀ v w, (inner ℂ (fX v) (fX w) : ℂ) = inner ℂ (fY v) (fY w) := by
    intro v w
    rw [hfX, hfY, key X v w, key Y v w, h]
  have hnormeq : ∀ v, ‖fY v‖ = ‖fX v‖ := by
    intro v
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hinner v v]
  have hker : LinearMap.ker fX = LinearMap.ker fY := by
    ext v
    simp only [LinearMap.mem_ker, ← norm_eq_zero (E := EuclideanSpace ℂ (Fin m)), hnormeq v]
  -- Since `fX` and `fY` have the same kernel, `fX v ↦ fY v` is a well-defined linear map on
  -- the range of `fX`, and it is isometric.
  let g : (EuclideanSpace ℂ (Fin n) ⧸ LinearMap.ker fX) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Submodule.liftQ _ fY (le_of_eq hker)
  let e := fX.quotKerEquivRange
  let L0 : (LinearMap.range fX) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) := g ∘ₗ e.symm.toLinearMap
  have hL0 : ∀ (v : EuclideanSpace ℂ (Fin n)) (hv : fX v ∈ LinearMap.range fX),
      L0 ⟨fX v, hv⟩ = fY v := by
    intro v hv
    simp [L0, g, e, LinearMap.quotKerEquivRange_symm_apply_image]
  have hnorm : ∀ z : LinearMap.range fX, ‖L0 z‖ = ‖z‖ := by
    rintro ⟨z, v, rfl⟩
    rw [hL0 v]
    simpa using hnormeq v
  let L : (LinearMap.range fX) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) := ⟨L0, hnorm⟩
  -- Extend the isometry to the whole space.
  let M : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) := L.extend
  have hM : ∀ v, M (fX v) = fY v := by
    intro v
    have h1 := L.extend_apply ⟨fX v, LinearMap.mem_range_self _ v⟩
    simpa [M, L, hL0] using h1
  set W : Matrix (Fin m) (Fin m) ℂ := Matrix.toEuclideanLin.symm M.toLinearMap with hWdef
  have hW : Matrix.toEuclideanLin W = M.toLinearMap := by
    rw [hWdef, LinearEquiv.apply_symm_apply]
  refine ⟨W, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    apply Matrix.toEuclideanLin.injective
    refine LinearMap.ext fun v => ?_
    rw [hmulcomp, hW, Matrix.toEuclideanLin_conjTranspose_eq_adjoint W, hW]
    have h2 : LinearMap.adjoint M.toLinearMap (M v) = v := by
      refine ext_inner_left ℂ fun x => ?_
      rw [LinearMap.adjoint_inner_right]
      exact M.inner_map_map x v
    simpa using h2
  · apply Matrix.toEuclideanLin.injective
    refine LinearMap.ext fun v => ?_
    rw [hmulcomp, hW]
    exact hM v

/-- Two purifications of the same mixed state with the same ancilla differ by a unitary acting
on the ancilla. -/
theorem purification_unique {n m : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ}
    {ψ chi : Matrix (Fin n) (Fin m) ℂ} (hψ : IsPurification ρ ψ) (hchi : IsPurification ρ chi) :
    ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, chi = ψ * U := by
  rw [isPurification_iff] at hψ hchi
  obtain ⟨W, hW, hWeq⟩ := exists_unitary_mul_eq ψᴴ chiᴴ (by simpa using hψ.trans hchi.symm)
  have hstar : Wᴴ ∈ Matrix.unitaryGroup (Fin m) ℂ := by
    have h1 := Matrix.mem_unitaryGroup_iff'.1 hW
    rw [Matrix.mem_unitaryGroup_iff]
    simpa [Matrix.star_eq_conjTranspose] using h1
  refine ⟨Wᴴ, hstar, ?_⟩
  have h2 := congrArg Matrix.conjTranspose hWeq
  simpa [Matrix.conjTranspose_mul] using h2.symm

/-- **Existence and uniqueness of purifications.**

Every mixed state `ρ` (a positive semidefinite matrix of trace one) on an `n`-dimensional system
admits a purification: a unit vector `ψ` of the composite system `ℂⁿ ⊗ ℂⁿ` whose reduced state,
obtained by tracing out the ancilla, is `ρ`.

Moreover the purification is unique up to a unitary (an isometry) acting on the ancilla alone:
any two purifications `ψ`, `chi` of `ρ` with the same ancilla are related by `chi = ψ * U` with `U`
unitary. -/
theorem purification_exists {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (∃ ψ : Matrix (Fin n) (Fin n) ℂ, IsPurification ρ ψ ∧ ∑ i, ∑ k, ‖ψ i k‖ ^ 2 = 1) ∧
      ∀ (m : ℕ) (ψ chi : Matrix (Fin n) (Fin m) ℂ), IsPurification ρ ψ → IsPurification ρ chi →
        ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, chi = ψ * U := by
  constructor
  · -- The canonical purification is `ρ ^ (1/2)`.
    have hmul : CFC.sqrt ρ * (CFC.sqrt ρ)ᴴ = ρ := by
      have h1 : (CFC.sqrt ρ).PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
      rw [h1.isHermitian.eq]
      exact CFC.sqrt_mul_sqrt_self (ha := hpsd.nonneg) ρ
    refine ⟨CFC.sqrt ρ, (isPurification_iff ρ _).2 hmul, ?_⟩
    set ψ := CFC.sqrt ρ with hψ
    have hc : ((∑ i, ∑ k, ‖ψ i k‖ ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast
      rw [← htr, ← hmul]
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.mul_conj]
      push_cast [← Complex.sq_norm]
      ring
    exact_mod_cast hc
  · intro m ψ chi hψ hchi
    exact purification_unique hψ hchi

/-- **Uniqueness up to an isometry of the ancilla.** If the ancilla of the second purification is
at least as large as that of the first, the two purifications are related by an isometry `V`
(`V * Vᴴ = 1`) acting on the ancilla alone. -/
theorem purification_unique_up_to_isometry {n m m' : ℕ} (hmm : m ≤ m')
    (ρ : Matrix (Fin n) (Fin n) ℂ) (ψ : Matrix (Fin n) (Fin m) ℂ)
    (chi : Matrix (Fin n) (Fin m') ℂ) (hψ : IsPurification ρ ψ) (hchi : IsPurification ρ chi) :
    ∃ V : Matrix (Fin m) (Fin m') ℂ, V * Vᴴ = 1 ∧ chi = ψ * V := by
  -- Embed the smaller ancilla into the larger one.
  set E : Matrix (Fin m) (Fin m') ℂ :=
    Matrix.of (fun i j => if (j : ℕ) = (i : ℕ) then (1 : ℂ) else 0) with hE
  have hEE : E * Eᴴ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (Fin.castLE hmm i) (Finset.mem_univ _)]
    · simp [hE, Matrix.conjTranspose_apply, Matrix.one_apply, Fin.ext_iff, eq_comm]
    · intro b _ hb
      have hbi : (b : ℕ) ≠ (i : ℕ) := fun hbi => hb (Fin.ext hbi)
      simp [hE, Matrix.conjTranspose_apply, hbi]
  have hψ' : IsPurification ρ (ψ * E) := by
    rw [isPurification_iff] at hψ ⊢
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc E Eᴴ ψᴴ, hEE,
      Matrix.one_mul]
    exact hψ
  obtain ⟨U, hU, hUeq⟩ := purification_unique hψ' hchi
  have hUU : U * Uᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hU
  refine ⟨E * U, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ Eᴴ, hUU,
      Matrix.one_mul, hEE]
  · rw [hUeq, Matrix.mul_assoc]

end QI

