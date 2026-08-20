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

Every mixed state has a purification, unique up to a unitary on the ancilla.

A mixed state on an `n`-dimensional Hilbert space `H` is a positive semidefinite matrix `ρ`
of trace one.  A pure state of the composite system `H ⊗ K`, with `K` an `m`-dimensional
ancilla, is encoded by its matrix of coefficients `psi : Matrix (Fin n) (Fin m) ℂ` in the
product basis, and the partial trace over the ancilla is `reducedDensity psi = psi * psiᴴ`.

The uniqueness statement is the operator fact `A Aᴴ = B Bᴴ → ∃ U unitary, B = A U`, which we
derive from `LinearIsometry.extend`: the assignment `Aᴴ x ↦ Bᴴ x` is a well-defined isometry
on `range Aᴴ` and extends to an isometry of the whole space.
-/

open Matrix

open scoped ComplexOrder MatrixOrder

namespace QI

noncomputable section

/-- The reduced density matrix (partial trace over the ancilla) of the pure state `|ψ⟩⟨ψ|`,
where the vector `ψ` of the composite system `H ⊗ K` (`H` of dimension `n`, ancilla `K` of
dimension `m`) is encoded by its coefficient matrix `psi` in the product basis,
`ψ = ∑ i, ∑ j, psi i j • (e i ⊗ f j)`. -/
def reducedDensity {n m : ℕ} (psi : Matrix (Fin n) (Fin m) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => ∑ j, psi i j * star (psi k j)

lemma reducedDensity_eq_mul_conjTranspose {n m : ℕ} (psi : Matrix (Fin n) (Fin m) ℂ) :
    reducedDensity psi = psi * psiᴴ := by
  ext i k
  simp [reducedDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]

section Isometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- If `a ∘ a* = b ∘ b*` then `a*` and `b*` have the same norms pointwise. -/
lemma norm_adjoint_eq_of_comp_adjoint_eq {a b : E →ₗ[ℂ] E}
    (h : a ∘ₗ LinearMap.adjoint a = b ∘ₗ LinearMap.adjoint b) (x : E) :
    ‖LinearMap.adjoint a x‖ = ‖LinearMap.adjoint b x‖ := by
  have key : ∀ c : E →ₗ[ℂ] E, (‖LinearMap.adjoint c x‖ : ℝ) ^ 2
      = RCLike.re (inner ℂ x ((c ∘ₗ LinearMap.adjoint c) x)) := by
    intro c
    have h1 : inner ℂ (LinearMap.adjoint c x) (LinearMap.adjoint c x)
        = inner ℂ x (c (LinearMap.adjoint c x)) := LinearMap.adjoint_inner_left _ _ _
    have h2 := @inner_self_eq_norm_sq ℂ E _ _ _ (LinearMap.adjoint c x)
    simp only [LinearMap.comp_apply]
    rw [← h1, ← h2]
  have ha := key a
  rw [h] at ha
  have hsq : ‖LinearMap.adjoint a x‖ ^ 2 = ‖LinearMap.adjoint b x‖ ^ 2 := by rw [ha, key b]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Two operators with the same "square" `a a* = b b*` have adjoints related by a linear
isometry of the whole space: there is an isometry `W` with `W (a* x) = b* x`. -/
lemma exists_isometry_of_comp_adjoint_eq {a b : E →ₗ[ℂ] E}
    (h : a ∘ₗ LinearMap.adjoint a = b ∘ₗ LinearMap.adjoint b) :
    ∃ W : E →ₗᵢ[ℂ] E, ∀ x, W (LinearMap.adjoint a x) = LinearMap.adjoint b x := by
  set A' := LinearMap.adjoint a with hA'
  set B' := LinearMap.adjoint b with hB'
  have hnorm : ∀ x, ‖A' x‖ = ‖B' x‖ := norm_adjoint_eq_of_comp_adjoint_eq h
  have hker : LinearMap.ker A' ≤ LinearMap.ker B' := by
    intro x hx
    have hx0 : ‖B' x‖ = 0 := by rw [← hnorm x, LinearMap.mem_ker.mp hx, norm_zero]
    simpa using norm_eq_zero.mp hx0
  -- `B'` factors through `E ⧸ ker A' ≃ range A'`, giving the isometry on `range A'`
  let f : (E ⧸ LinearMap.ker A') →ₗ[ℂ] E := (LinearMap.ker A').liftQ B' hker
  let e := A'.quotKerEquivRange
  let Lm : (LinearMap.range A') →ₗ[ℂ] E := f ∘ₗ (e.symm : LinearMap.range A' →ₗ[ℂ] _)
  have hLm : ∀ x : E, Lm ⟨A' x, LinearMap.mem_range_self _ x⟩ = B' x := by
    intro x
    have he : e (Submodule.Quotient.mk x) = ⟨A' x, LinearMap.mem_range_self _ x⟩ :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk A' x)
    have hs : (e.symm ⟨A' x, LinearMap.mem_range_self _ x⟩) = Submodule.Quotient.mk x := by
      rw [← he, LinearEquiv.symm_apply_apply]
    simp [Lm, hs, f, Submodule.liftQ_apply]
  have hnm : ∀ y : (LinearMap.range A'), ‖Lm y‖ = ‖y‖ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    rw [hLm x]
    simpa using (hnorm x).symm
  let L : (LinearMap.range A') →ₗᵢ[ℂ] E := ⟨Lm, hnm⟩
  refine ⟨L.extend, fun x => ?_⟩
  have hext := L.extend_apply ⟨A' x, LinearMap.mem_range_self _ x⟩
  simpa [L, hLm x] using hext

/-- A linear isometry of a finite-dimensional space satisfies `W* ∘ W = id`. -/
lemma adjoint_comp_self_of_isometry (W : E →ₗᵢ[ℂ] E) :
    LinearMap.adjoint (W.toLinearMap) ∘ₗ W.toLinearMap = LinearMap.id := by
  refine LinearMap.ext fun v => ext_inner_right ℂ (fun w => ?_)
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  simp [W.inner_map_map]

end Isometry

section MatrixLin

variable {n : ℕ}

lemma toEuclideanLin_mul (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.toEuclideanLin (A * B) =
      Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
  ext v i
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

lemma toEuclideanLin_one :
    Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℂ) = LinearMap.id := by
  ext v i
  simp

/-- **Uniqueness of purifications up to a unitary on the ancilla** (matrix form):
if `A Aᴴ = B Bᴴ` then `B = A U` for a unitary `U`. -/
theorem exists_unitary_mul_of_mul_conjTranspose_eq (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ B = A * U := by
  have hadjA : LinearMap.adjoint (Matrix.toEuclideanLin A) = Matrix.toEuclideanLin Aᴴ :=
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  have hadjB : LinearMap.adjoint (Matrix.toEuclideanLin B) = Matrix.toEuclideanLin Bᴴ :=
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint B).symm
  have h' : Matrix.toEuclideanLin A ∘ₗ LinearMap.adjoint (Matrix.toEuclideanLin A)
      = Matrix.toEuclideanLin B ∘ₗ LinearMap.adjoint (Matrix.toEuclideanLin B) := by
    rw [hadjA, hadjB, ← toEuclideanLin_mul, ← toEuclideanLin_mul, h]
  obtain ⟨W, hW⟩ := exists_isometry_of_comp_adjoint_eq h'
  set M := Matrix.toEuclideanLin.symm (W.toLinearMap) with hM
  have hMlin : Matrix.toEuclideanLin M = W.toLinearMap := LinearEquiv.apply_symm_apply _ _
  have hMA : M * Aᴴ = Bᴴ := by
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul, hMlin, ← hadjA, ← hadjB]
    exact LinearMap.ext hW
  have hMM : Mᴴ * M = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul, toEuclideanLin_one, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      hMlin, adjoint_comp_self_of_isometry]
  refine ⟨Mᴴ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using mul_eq_one_comm.mp hMM
  · have hcong := congrArg Matrix.conjTranspose hMA
    simpa [Matrix.conjTranspose_mul] using hcong.symm

end MatrixLin

/-- Existence of a purification: a positive semidefinite `ρ` is `psi * psiᴴ` for some `psi`. -/
lemma exists_mul_conjTranspose_eq_of_posSemidef {n : ℕ} {rho : Matrix (Fin n) (Fin n) ℂ}
    (h : rho.PosSemidef) :
    ∃ psi : Matrix (Fin n) (Fin n) ℂ, psi * psiᴴ = rho := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 (Matrix.nonneg_iff_posSemidef.2 h)
  exact ⟨Bᴴ, by simpa [Matrix.star_eq_conjTranspose] using hB.symm⟩

lemma sum_normSq_eq_trace {n m : ℕ} (psi : Matrix (Fin n) (Fin m) ℂ) :
    ((∑ i, ∑ j, ‖psi i j‖ ^ 2 : ℝ) : ℂ) = (psi * psiᴴ).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj']

/-- **Purification exists and is unique up to a unitary on the ancilla.**

For every mixed state `ρ` on an `n`-dimensional Hilbert space (a positive semidefinite matrix
of trace one) there is a unit vector `psi` of the doubled system `H ⊗ K` (`K` a copy of `H`)
whose partial trace over the ancilla `K` is `ρ`; and any two such purifications differ by a
unitary acting on the ancilla only. -/
theorem purification_exists {n : ℕ} (rho : Matrix (Fin n) (Fin n) ℂ)
    (hrho : rho.PosSemidef) (htr : rho.trace = 1) :
    (∃ psi : Matrix (Fin n) (Fin n) ℂ,
        reducedDensity psi = rho ∧ ∑ i, ∑ j, ‖psi i j‖ ^ 2 = 1) ∧
      (∀ psi₁ psi₂ : Matrix (Fin n) (Fin n) ℂ,
        reducedDensity psi₁ = rho → reducedDensity psi₂ = rho →
        ∃ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
          psi₂ = psi₁ * U) := by
  constructor
  · obtain ⟨psi, hpsi⟩ := exists_mul_conjTranspose_eq_of_posSemidef hrho
    refine ⟨psi, by rw [reducedDensity_eq_mul_conjTranspose, hpsi], ?_⟩
    have hsum := sum_normSq_eq_trace psi
    rw [hpsi, htr] at hsum
    exact_mod_cast hsum
  · intro psi₁ psi₂ h₁ h₂
    rw [reducedDensity_eq_mul_conjTranspose] at h₁ h₂
    exact exists_unitary_mul_of_mul_conjTranspose_eq psi₁ psi₂ (h₁.trans h₂.symm)

end

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

