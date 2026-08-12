import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/
def vecm (X : Matrix n m ℂ) : n × m → ℂ := fun p => X p.1 p.2

/-- The inverse of `vecm`. -/
def unvecm (x : n × m → ℂ) : Matrix n m ℂ := Matrix.of fun i j => x (i, j)

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
@[simp] lemma unvecm_vecm (X : Matrix n m ℂ) : unvecm (vecm X) = X := rfl

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
@[simp] lemma vecm_unvecm (x : n × m → ℂ) : vecm (unvecm x) = x := by
  funext p; rfl

omit [DecidableEq n] [DecidableEq m] in
/-- The Hilbert–Schmidt inner product in vectorized form. -/
lemma dot_vecm (X Y : Matrix n m ℂ) : star (vecm X) ⬝ᵥ vecm Y = trace (Xᴴ * Y) := by
  simp [vecm, dotProduct, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, diag]
  rw [Finset.sum_comm]

omit [DecidableEq n] [DecidableEq m] in
/-- Action of a Kronecker product on a vectorized matrix. -/
lemma kron_mulVecm (A : Matrix n n ℂ) (B : Matrix m m ℂ) (X : Matrix n m ℂ) :
    (A ⊗ₖ Bᵀ) *ᵥ vecm X = vecm (A * X * B) := by
  funext p
  simp [vecm, mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]

/-! ### The modular operator -/

/-- The (relative) modular operator `σ ⊗ (ρ⁻¹)ᵀ`, acting on vectorized matrices by
`X ↦ σ X ρ⁻¹`. -/
noncomputable def modOp (σ ρ : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := σ ⊗ₖ (ρ⁻¹)ᵀ

lemma modOp_posDef {σ ρ : Matrix n n ℂ} (hσ : σ.PosDef) (hρ : ρ.PosDef) :
    (modOp σ ρ).PosDef :=
  Matrix.PosDef.kronecker hσ (hρ.inv.transpose)

lemma modOp_mulVec (σ ρ : Matrix n n ℂ) (X : Matrix n n ℂ) :
    modOp σ ρ *ᵥ vecm X = vecm (σ * X * ρ⁻¹) := kron_mulVecm _ _ _

/-! ### Relative entropy -/

/-- Umegaki relative entropy `Tr ρ log ρ - Tr ρ log σ`. -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (trace (ρ * cfc Real.log ρ)).re - (trace (ρ * cfc Real.log σ)).re

/-! ### Square roots -/

lemma sqrt_mul_sqrt {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    CFC.sqrt ρ * CFC.sqrt ρ = ρ :=
  CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg

lemma sqrt_posDef {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) : (CFC.sqrt ρ).PosDef :=
  isStrictlyPositive_iff_posDef.mp (isStrictlyPositive_iff_posDef.mpr hρ).sqrt

lemma sqrt_herm {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
  (sqrt_posDef hρ).isHermitian

/-! ### The relative entropy as a quadratic form -/

/-- `relEntropy ρ σ` is minus the quadratic form of `log (modOp σ ρ)` at `vecm √ρ`. -/
theorem relEntropy_eq_quadForm {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEntropy ρ σ
      = -(star (vecm (CFC.sqrt ρ)) ⬝ᵥ
            ((cfc Real.log (modOp σ ρ)) *ᵥ vecm (CFC.sqrt ρ))).re := by
  have hlog : cfc Real.log (modOp σ ρ)
      = (cfc Real.log σ) ⊗ₖ (1 : Matrix n n ℂ)
        + (1 : Matrix n n ℂ) ⊗ₖ (- (cfc Real.log ρ))ᵀ := by
    rw [modOp, cfc_log_kron hσ (hρ.inv.transpose), cfc_transpose hρ.inv.isHermitian,
      cfc_log_inv hρ]
  rw [hlog]
  set s := CFC.sqrt ρ with hs
  have hss : s * s = ρ := sqrt_mul_sqrt hρ
  have hsH : sᴴ = s := sqrt_herm hρ
  have h1 : ((cfc Real.log σ) ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ vecm s
      = vecm ((cfc Real.log σ) * s * 1) := by
    have := kron_mulVecm (cfc Real.log σ) (1 : Matrix n n ℂ) s
    rwa [Matrix.transpose_one] at this
  have h2 : ((1 : Matrix n n ℂ) ⊗ₖ (- (cfc Real.log ρ))ᵀ) *ᵥ vecm s
      = vecm (1 * s * (- cfc Real.log ρ)) := kron_mulVecm _ _ _
  rw [Matrix.add_mulVec, h1, h2, dotProduct_add, Complex.add_re, dot_vecm, dot_vecm]
  rw [Matrix.mul_one, Matrix.one_mul, hsH]
  have e1 : trace (s * ((cfc Real.log σ) * s)) = trace (ρ * cfc Real.log σ) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hss,
      Matrix.trace_mul_comm]
  have e2 : trace (s * (s * (- cfc Real.log ρ))) = - trace (ρ * cfc Real.log ρ) := by
    rw [← Matrix.mul_assoc, hss, Matrix.mul_neg, Matrix.trace_neg]
  rw [e1, e2, relEntropy]
  simp
  ring

/-- The squared norm of `vecm √ρ` is the trace of `ρ`. -/
lemma dot_vecm_sqrt_self {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    star (vecm (CFC.sqrt ρ)) ⬝ᵥ vecm (CFC.sqrt ρ) = trace ρ := by
  rw [dot_vecm, sqrt_herm hρ, sqrt_mul_sqrt hρ]

/-- Integral formula for the relative entropy. -/
theorem relEntropy_eq_neg_integral {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEntropy ρ σ
      = - ∫ t in Set.Ioi (0:ℝ), resolvIntegrand (modOp σ ρ) (vecm (CFC.sqrt ρ)) t := by
  have hpd := modOp_posDef hσ hρ
  rw [relEntropy_eq_quadForm hρ hσ,
    quadForm_log_eq_integral hpd.isHermitian hpd.eigenvalues_pos]

/-! ### The variational characterization of resolvent quadratic forms -/

lemma posDef_mul_inv {S : Matrix N N ℂ} (hS : S.PosDef) : S * S⁻¹ = 1 :=
  Matrix.mul_nonsing_inv S (Matrix.isUnit_iff_isUnit_det _ |>.mp hS.isUnit)

lemma posDef_inv_mul {S : Matrix N N ℂ} (hS : S.PosDef) : S⁻¹ * S = 1 :=
  Matrix.nonsing_inv_mul S (Matrix.isUnit_iff_isUnit_det _ |>.mp hS.isUnit)

omit [DecidableEq N] in
lemma dot_herm_symm {S : Matrix N N ℂ} (hS : S.IsHermitian) (x y : N → ℂ) :
    star x ⬝ᵥ (S *ᵥ y) = starRingEnd ℂ (star y ⬝ᵥ (S *ᵥ x)) := by
  rw [dotProduct_mulVec, show star x ᵥ* S = star (S *ᵥ x) by rw [Matrix.star_mulVec, hS],
    star_dotProduct]
  simp

omit [DecidableEq N] in
lemma quad_expand (S : Matrix N N ℂ) (x y : N → ℂ) :
    star (x - y) ⬝ᵥ (S *ᵥ (x - y))
      = star x ⬝ᵥ (S *ᵥ x) - star x ⬝ᵥ (S *ᵥ y) - star y ⬝ᵥ (S *ᵥ x)
        + star y ⬝ᵥ (S *ᵥ y) := by
  simp only [Matrix.mulVec_sub, star_sub, dotProduct_sub, sub_dotProduct]
  ring

/-- **Completing the square**: the resolvent quadratic form dominates the associated
"linear minus quadratic" functional. -/
theorem variational_le {S : Matrix N N ℂ} (hS : S.PosDef) (xi x : N → ℂ) :
    2 * (star x ⬝ᵥ xi).re - (star x ⬝ᵥ (S *ᵥ x)).re
      ≤ (star xi ⬝ᵥ (S⁻¹ *ᵥ xi)).re := by
  set y := S⁻¹ *ᵥ xi with hy
  have hSy : S *ᵥ y = xi := by
    rw [hy, Matrix.mulVec_mulVec, posDef_mul_inv hS, Matrix.one_mulVec]
  have h0 : (0:ℝ) ≤ (star (x - y) ⬝ᵥ (S *ᵥ (x - y))).re := by
    have := hS.posSemidef.dotProduct_mulVec_nonneg (x - y)
    exact_mod_cast Complex.le_def.mp this |>.1
  rw [quad_expand S x y, hSy] at h0
  have h1 : (star y ⬝ᵥ (S *ᵥ x)).re = (star x ⬝ᵥ xi).re := by
    rw [dot_herm_symm hS.isHermitian y x, hSy]
    simp
  have h2 : (star y ⬝ᵥ xi).re = (star xi ⬝ᵥ (S⁻¹ *ᵥ xi)).re := by
    rw [hy, star_dotProduct]
    simp
  simp only [Complex.sub_re, Complex.add_re] at h0
  rw [h1, h2] at h0
  linarith

/-- The bound in `variational_le` is attained at `x = S⁻¹ ξ`. -/
theorem variational_eq {S : Matrix N N ℂ} (hS : S.PosDef) (xi : N → ℂ) :
    2 * (star (S⁻¹ *ᵥ xi) ⬝ᵥ xi).re - (star (S⁻¹ *ᵥ xi) ⬝ᵥ (S *ᵥ (S⁻¹ *ᵥ xi))).re
      = (star xi ⬝ᵥ (S⁻¹ *ᵥ xi)).re := by
  have hSy : S *ᵥ (S⁻¹ *ᵥ xi) = xi := by
    rw [Matrix.mulVec_mulVec, posDef_mul_inv hS, Matrix.one_mulVec]
  have h2 : (star (S⁻¹ *ᵥ xi) ⬝ᵥ xi).re = (star xi ⬝ᵥ (S⁻¹ *ᵥ xi)).re := by
    rw [star_dotProduct]; simp
  rw [hSy, h2]
  ring

end QI

import Mathlib

/-!
# Spectral tools for Hermitian matrices

Functional calculus for Hermitian complex matrices computed through an arbitrary
unitary diagonalization, quadratic forms, and the integral representation of the
logarithm.
-/

open Matrix Filter MeasureTheory
open scoped ComplexOrder
open scoped BigOperators Topology

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal embedding of `n → ℂ` into matrices, as a star algebra homomorphism. -/
noncomputable def diagSAH : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun := Matrix.diagonal
  map_one' := by simp
  map_mul' x y := by simp [Matrix.diagonal_mul_diagonal]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.diagonal_add]
  commutes' r := by
    ext i j; by_cases h : i = j <;>
      simp [Matrix.diagonal, h, Algebra.algebraMap_eq_smul_one]
  map_star' x := by ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, eq_comm]

/-- The continuous functional calculus of a real diagonal matrix is diagonal. -/
theorem cfc_diagonal (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (diagonal fun i => ((d i : ℝ) : ℂ)) = diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  have key : ∀ i : n, spectrum ℝ ((d i : ℝ) : ℂ) = {d i} := fun i =>
    spectrum.scalar_eq (𝕜 := ℝ) (A := ℂ) (d i)
  have hd : IsSelfAdjoint (fun i => ((d i : ℝ) : ℂ)) := by ext i; simp
  have hsp : spectrum ℝ (fun i => ((d i : ℝ) : ℂ)) = Set.range d := by
    rw [Pi.spectrum_eq]
    ext r
    simp only [Set.mem_iUnion, key, Set.mem_singleton_iff, Set.mem_range]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  have hcont : ContinuousOn f (spectrum ℝ (fun i => ((d i : ℝ) : ℂ))) := by
    rw [hsp]; exact (Set.finite_range d).continuousOn f
  have hcd : Continuous (diagSAH : (n → ℂ) → Matrix n n ℂ) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun v : n → ℂ => Matrix.diagonal v i j
    simp only [Matrix.diagonal_apply]
    split <;> fun_prop
  have hself : IsSelfAdjoint (diagSAH (fun i => ((d i : ℝ) : ℂ))) := by
    rw [IsSelfAdjoint, ← map_star, hd.star_eq]
  have h := (diagSAH (n := n)).map_cfc f (fun i => ((d i : ℝ) : ℂ)) hcont hcd hd hself
  have hpi : (cfc f (fun i => ((d i : ℝ) : ℂ))) = fun i => ((f (d i) : ℝ) : ℂ) := by
    rw [cfc_map_pi (S := ℂ) f _ (by
      rw [show (⋃ i, spectrum ℝ ((d i : ℝ) : ℂ)) = Set.range d from by
        rw [← Pi.spectrum_eq]; exact hsp]
      exact (Set.finite_range d).continuousOn f) hd (fun i => by rw [IsSelfAdjoint]; simp)]
    funext i
    rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, cfc_algebraMap]
    rfl
  have hdd : diagSAH (fun i => ((d i : ℝ) : ℂ)) = diagonal (fun i => ((d i : ℝ) : ℂ)) := rfl
  rw [← hdd, ← h, hpi]
  rfl

/-- The continuous functional calculus commutes with unitary conjugation. -/
theorem cfc_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (U * A * Uᴴ) = U * (cfc f A) * Uᴴ := by
  set φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ⟨U, hU⟩ with hφ
  have happ : ∀ X, φ X = U * X * Uᴴ := by
    intro X; rw [hφ, Unitary.conjStarAlgAut_apply]; rfl
  have hcont : Continuous (φ : Matrix n n ℂ → Matrix n n ℂ) := by
    have h2 : (fun X => φ X) = fun X => U * X * Uᴴ := by funext X; exact happ X
    rw [show (φ : Matrix n n ℂ → Matrix n n ℂ) = fun X => φ X from rfl, h2]; fun_prop
  have hst : IsSelfAdjoint (φ A) := by
    rw [IsSelfAdjoint, ← map_star]; congr 1
  have h := StarAlgHomClass.map_cfc (S := ℂ) φ f A
    (Set.Finite.continuousOn (Set.toFinite _) f) hcont hA hst
  rw [← happ, ← happ, ← h]

/-- **Functional calculus through an arbitrary unitary diagonalization.** -/
theorem cfc_of_diagonalization {A U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    (d : n → ℝ) (hA : A = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ) (f : ℝ → ℝ) :
    cfc f A = U * diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * Uᴴ := by
  have hherm : (diagonal (fun i => ((d i : ℝ) : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, diagonal_conjTranspose]
    simp [Pi.star_def]
  rw [hA, cfc_unitary_conj hU hherm f, cfc_diagonal]

/-- The quadratic form of a matrix conjugate to a diagonal one. -/
theorem quadForm_conj_diagonal (U : Matrix n n ℂ) (v : n → ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((U * diagonal v * Uᴴ) *ᵥ x)
      = ∑ k, v k * (starRingEnd ℂ ((Uᴴ *ᵥ x) k) * ((Uᴴ *ᵥ x) k)) := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    show star x ᵥ* U = star (Uᴴ *ᵥ x) by rw [Matrix.star_mulVec]; simp]
  simp [Matrix.mulVec_diagonal, dotProduct, mul_comm, mul_assoc]

/-- The squared moduli of the coordinates of `x` in the eigenbasis of `A`. -/
noncomputable def specCoeff {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) (k : n) : ℝ :=
  Complex.normSq (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ x) k)

lemma specCoeff_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) (k : n) :
    0 ≤ specCoeff hA x k := Complex.normSq_nonneg _

lemma eigen_unitary {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ((hA.eigenvectorUnitary : Matrix n n ℂ)) * ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ = 1 := by
  have := hA.eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff] at this
  exact this

lemma eigen_decomp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

theorem quadForm_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) (x : n → ℂ) :
    star x ⬝ᵥ ((cfc f A) *ᵥ x)
      = ∑ k, ((f (hA.eigenvalues k) * specCoeff hA x k : ℝ) : ℂ) := by
  rw [show cfc f A = ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
      diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ from
    cfc_of_diagonalization hA.eigenvectorUnitary.2 _ (eigen_decomp hA) f,
    quadForm_conj_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, specCoeff, Complex.normSq_eq_conj_mul_self]

lemma eigen_unitary' {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ * ((hA.eigenvectorUnitary : Matrix n n ℂ)) = 1 := by
  have h := Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  rw [Matrix.star_eq_conjTranspose] at h
  exact h

lemma conj_diagonal_add (U : Matrix n n ℂ) (v w : n → ℂ) :
    U * diagonal v * Uᴴ + U * diagonal w * Uᴴ = U * diagonal (v + w) * Uᴴ := by
  rw [← Matrix.add_mul, ← Matrix.mul_add]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

lemma smul_one_conj (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (t : ℂ) :
    t • (1 : Matrix n n ℂ) = U * diagonal (fun _ : n => t) * Uᴴ := by
  rw [← Matrix.smul_one_eq_diagonal, mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hU]

/-- Spectral form of the shifted matrix `A + t`. -/
lemma add_const_decomp {A : Matrix n n ℂ} (hA : A.IsHermitian) (t : ℝ) :
    A + (t : ℂ) • 1 = ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
      diagonal (fun k => ((hA.eigenvalues k + t : ℝ) : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ := by
  conv_lhs => rw [eigen_decomp hA, smul_one_conj _ (eigen_unitary hA) ((t : ℝ) : ℂ)]
  have hfun : ((fun i => ((hA.eigenvalues i : ℝ) : ℂ)) + fun _ : n => ((t : ℝ) : ℂ))
      = fun k => ((hA.eigenvalues k + t : ℝ) : ℂ) := by
    funext k; simp
  rw [conj_diagonal_add, hfun]

/-- Spectral form of the resolvent. -/
lemma resolvent_decomp {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 ≤ hA.eigenvalues k) {t : ℝ} (ht : 0 < t) :
    (A + (t : ℂ) • 1)⁻¹ = ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
      diagonal (fun k => (((hA.eigenvalues k + t)⁻¹ : ℝ) : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [add_const_decomp hA t]
  have hne : ∀ k, ((hA.eigenvalues k + t : ℝ) : ℂ) ≠ 0 := by
    intro k
    have : (0 : ℝ) < hA.eigenvalues k + t := by
      have := hpos k
      linarith
    exact_mod_cast this.ne'
  calc ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
        diagonal (fun k => ((hA.eigenvalues k + t : ℝ) : ℂ)) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ *
        (((hA.eigenvectorUnitary : Matrix n n ℂ)) *
        diagonal (fun k => (((hA.eigenvalues k + t)⁻¹ : ℝ) : ℂ)) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ)
      = ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
        (diagonal (fun k => ((hA.eigenvalues k + t : ℝ) : ℂ)) *
          (((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ *
            ((hA.eigenvectorUnitary : Matrix n n ℂ))) *
          diagonal (fun k => (((hA.eigenvalues k + t)⁻¹ : ℝ) : ℂ))) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by
          rw [eigen_unitary' hA, Matrix.mul_one, diagonal_mul_diagonal]
          rw [show (fun k => ((hA.eigenvalues k + t : ℝ) : ℂ) *
              (((hA.eigenvalues k + t)⁻¹ : ℝ) : ℂ)) = fun _ : n => (1 : ℂ) from by
            funext k
            rw [← Complex.ofReal_mul, mul_inv_cancel₀]
            · simp
            · exact_mod_cast (by simpa using hne k : ((hA.eigenvalues k + t : ℝ) : ℂ) ≠ 0)]
          rw [show diagonal (fun _ : n => (1 : ℂ)) = 1 from by simp, Matrix.mul_one,
            eigen_unitary hA]

/-- The quadratic form of the resolvent. -/
theorem quadForm_resolvent {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 ≤ hA.eigenvalues k) {t : ℝ} (ht : 0 < t) (x : n → ℂ) :
    star x ⬝ᵥ ((A + (t : ℂ) • 1)⁻¹ *ᵥ x)
      = ∑ k, (((hA.eigenvalues k + t)⁻¹ * specCoeff hA x k : ℝ) : ℂ) := by
  rw [resolvent_decomp hA hpos ht, quadForm_conj_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, specCoeff, Complex.normSq_eq_conj_mul_self]

theorem quadForm_self {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ x = ∑ k, ((specCoeff hA x k : ℝ) : ℂ) := by
  have h1 : ((hA.eigenvectorUnitary : Matrix n n ℂ)) * diagonal (fun _ : n => (1 : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ = 1 := by
    rw [show diagonal (fun _ : n => (1 : ℂ)) = 1 from by simp, Matrix.mul_one, eigen_unitary hA]
  have h2 := quadForm_conj_diagonal (hA.eigenvectorUnitary : Matrix n n ℂ) (fun _ => (1:ℂ)) x
  rw [h1] at h2
  simp only [Matrix.one_mulVec, one_mul] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [specCoeff, Complex.normSq_eq_conj_mul_self]

/-- Integral representation of the real logarithm:
`log l = ∫_0^∞ (1/(1+t) - 1/(l+t)) dt`, together with integrability of the integrand. -/
theorem logRepr {l : ℝ} (hl : 0 < l) :
    (IntegrableOn (fun t : ℝ => 1/(1+t) - 1/(l+t)) (Set.Ioi 0)) ∧
      ∫ t in Set.Ioi (0:ℝ), (1/(1+t) - 1/(l+t)) = Real.log l := by
  set g : ℝ → ℝ := fun t => Real.log (1+t) - Real.log (l+t) with hg
  have hderiv : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt g (1/(1+t) - 1/(l+t)) t := by
    intro t ht
    simp only [Set.mem_Ioi] at ht
    have h1 : HasDerivAt (fun t : ℝ => Real.log (1+t)) (1/(1+t)) t := by
      have := (Real.hasDerivAt_log (x := 1+t) (by positivity)).comp t
        ((hasDerivAt_id t).const_add 1)
      simpa [one_div] using this
    have h2 : HasDerivAt (fun t : ℝ => Real.log (l+t)) (1/(l+t)) t := by
      have := (Real.hasDerivAt_log (x := l+t) (by positivity)).comp t
        ((hasDerivAt_id t).const_add l)
      simpa [one_div] using this
    exact h1.sub h2
  have hcont : ContinuousWithinAt g (Set.Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.sub
    · exact (Real.continuousAt_log (by norm_num)).comp (by fun_prop)
    · exact (Real.continuousAt_log (by simpa using hl.ne')).comp (by fun_prop)
  have htend : Tendsto g atTop (𝓝 0) := by
    have hdiv : Tendsto (fun t : ℝ => (1 - l)/(l+t)) atTop (𝓝 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_left _ l tendsto_id
    have h1 : Tendsto (fun t : ℝ => (1+t)/(l+t)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun t : ℝ => 1 + (1 - l)/(l+t)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add hdiv
      rw [add_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      field_simp
      ring
    have h2 : Tendsto (fun t : ℝ => Real.log ((1+t)/(l+t))) atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num)).tendsto.comp h1
    rw [Real.log_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.log_div (by positivity) (by positivity)]
  have hg0 : g 0 = - Real.log l := by simp [hg]
  have hint : IntegrableOn (fun t : ℝ => 1/(1+t) - 1/(l+t)) (Set.Ioi 0) := by
    rcases le_total 1 l with h | h
    · refine integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun t ht => ?_) htend
      simp only [Set.mem_Ioi] at ht
      rw [sub_nonneg, one_div, one_div]
      exact inv_anti₀ (by positivity) (by linarith)
    · have hneg : IntegrableOn (fun t : ℝ => -(1/(1+t) - 1/(l+t))) (Set.Ioi 0) := by
        refine integrableOn_Ioi_deriv_of_nonneg (g := fun t => -g t) (hcont.neg)
          (fun t ht => (hderiv t ht).neg) (fun t ht => ?_) (by simpa using htend.neg)
        simp only [Set.mem_Ioi] at ht
        rw [neg_nonneg, sub_nonpos, one_div, one_div]
        exact inv_anti₀ (by positivity) (by linarith)
      have h3 := hneg.neg
      simp only [Pi.neg_def, neg_neg] at h3
      exact h3
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend, hg0]
  ring

/-- The integrand of the integral representation of the logarithm's quadratic form. -/
noncomputable def resolvIntegrand (A : Matrix n n ℂ) (x : n → ℂ) (t : ℝ) : ℝ :=
  (star x ⬝ᵥ x).re * (1/(1+t)) - (star x ⬝ᵥ ((A + (t : ℂ) • 1)⁻¹ *ᵥ x)).re

lemma resolvIntegrand_eq {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 ≤ hA.eigenvalues k) {t : ℝ} (ht : 0 < t) (x : n → ℂ) :
    resolvIntegrand A x t
      = ∑ k, specCoeff hA x k * (1/(1+t) - 1/(hA.eigenvalues k + t)) := by
  rw [resolvIntegrand, quadForm_self hA x, quadForm_resolvent hA hpos ht x]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_div, one_div]
  ring

lemma integrableOn_resolvIntegrand {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 < hA.eigenvalues k) (x : n → ℂ) :
    IntegrableOn (resolvIntegrand A x) (Set.Ioi 0) := by
  have hsum : IntegrableOn
      (fun t => ∑ k, specCoeff hA x k * (1/(1+t) - 1/(hA.eigenvalues k + t))) (Set.Ioi 0) := by
    apply MeasureTheory.integrable_finset_sum
    intro k _
    exact ((logRepr (hpos k)).1).smul (specCoeff hA x k)
  exact hsum.congr_fun (fun t ht => (resolvIntegrand_eq hA (fun k => (hpos k).le) ht x).symm)
    measurableSet_Ioi

/-- **Integral representation of the quadratic form of the matrix logarithm.** -/
theorem quadForm_log_eq_integral {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 < hA.eigenvalues k) (x : n → ℂ) :
    (star x ⬝ᵥ ((cfc Real.log A) *ᵥ x)).re
      = ∫ t in Set.Ioi (0:ℝ), resolvIntegrand A x t := by
  have hcongr : ∫ t in Set.Ioi (0:ℝ), resolvIntegrand A x t
      = ∫ t in Set.Ioi (0:ℝ), ∑ k, specCoeff hA x k * (1/(1+t) - 1/(hA.eigenvalues k + t)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact resolvIntegrand_eq hA (fun k => (hpos k).le) ht x
  rw [hcongr, MeasureTheory.integral_finset_sum]
  · rw [quadForm_cfc hA Real.log x]
    simp only [Complex.re_sum, Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MeasureTheory.integral_const_mul, (logRepr (hpos k)).2]
    ring
  · intro k _
    exact ((logRepr (hpos k)).1).smul (specCoeff hA x k)

end QI

import RequestProject.Spectral

/-!
# Logarithms of Kronecker products, inverses and transposes
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Existence of a unitary diagonalization with real eigenvalues. -/
lemma exists_diagonalization {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ), U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      A = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ :=
  ⟨_, hA.eigenvalues, eigen_unitary hA, eigen_unitary' hA, eigen_decomp hA⟩

/-- Existence of a unitary diagonalization with positive eigenvalues. -/
lemma exists_diagonalization_pos {A : Matrix n n ℂ} (hA : A.PosDef) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ), U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ (∀ k, 0 < d k) ∧
      A = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ :=
  ⟨_, hA.isHermitian.eigenvalues, eigen_unitary _, eigen_unitary' _, hA.eigenvalues_pos,
    eigen_decomp _⟩

lemma unitary_of_mul {U : Matrix n n ℂ} (h1 : U * Uᴴ = 1) (h2 : Uᴴ * U = 1) :
    U ∈ unitary (Matrix n n ℂ) := Unitary.mem_iff.mpr ⟨h2, h1⟩

/-- Inverse of a matrix presented as a unitary conjugate of an invertible diagonal matrix. -/
lemma conj_diagonal_inv {U : Matrix n n ℂ} (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) {v : n → ℂ}
    (hv : ∀ k, v k ≠ 0) :
    (U * diagonal v * Uᴴ)⁻¹ = U * diagonal (fun k => (v k)⁻¹) * Uᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  calc U * diagonal v * Uᴴ * (U * diagonal (fun k => (v k)⁻¹) * Uᴴ)
      = U * (diagonal v * (Uᴴ * U) * diagonal (fun k => (v k)⁻¹)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hU', Matrix.mul_one, diagonal_mul_diagonal,
          show (fun k => v k * (v k)⁻¹) = fun _ : n => (1 : ℂ) from by
            funext k; exact mul_inv_cancel₀ (hv k),
          show diagonal (fun _ : n => (1 : ℂ)) = 1 from by simp, Matrix.mul_one, hU]

/-- The logarithm of the inverse of a positive definite matrix. -/
lemma cfc_log_inv {A : Matrix n n ℂ} (hA : A.PosDef) :
    cfc Real.log A⁻¹ = - cfc Real.log A := by
  obtain ⟨U, d, hU, hU', hdpos, hdec⟩ := exists_diagonalization_pos hA
  have hne : ∀ k, ((d k : ℝ) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hdpos k).ne'
  have hinv : A⁻¹ = U * diagonal (fun k => (((d k)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
    rw [hdec, conj_diagonal_inv hU hU' hne]
    congr 2
    funext k
    simp
  rw [cfc_of_diagonalization (unitary_of_mul hU hU') (fun k => (d k)⁻¹) hinv Real.log,
    cfc_of_diagonalization (unitary_of_mul hU hU') d hdec Real.log]
  have hfun : (fun k => ((Real.log ((d k)⁻¹) : ℝ) : ℂ))
      = (fun k => -((Real.log (d k) : ℝ) : ℂ)) := by
    funext k
    simp [Real.log_inv]
  rw [hfun, ← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]

/-- The functional calculus commutes with transposition of a Hermitian matrix. -/
lemma cfc_transpose {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f Aᵀ = (cfc f A)ᵀ := by
  obtain ⟨U, d, hU, hU', hdec⟩ := exists_diagonalization hA
  have hVH : (Uᴴᵀ)ᴴ = Uᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
  have hV1 : Uᴴᵀ * (Uᴴᵀ)ᴴ = 1 := by
    rw [hVH, ← Matrix.transpose_mul, hU, Matrix.transpose_one]
  have hV2 : (Uᴴᵀ)ᴴ * Uᴴᵀ = 1 := by
    rw [hVH, ← Matrix.transpose_mul, hU', Matrix.transpose_one]
  have hdiagT : ∀ g : ℝ → ℝ, (diagonal (fun i => ((g (d i) : ℝ) : ℂ)))ᵀ
      = diagonal (fun i => ((g (d i) : ℝ) : ℂ)) := by
    intro g
    ext i j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hdiagT0 : (diagonal (fun i => ((d i : ℝ) : ℂ)))ᵀ = diagonal (fun i => ((d i : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hdecT : Aᵀ = Uᴴᵀ * diagonal (fun i => ((d i : ℝ) : ℂ)) * (Uᴴᵀ)ᴴ := by
    conv_lhs => rw [hdec]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hVH, hdiagT0, Matrix.mul_assoc]
  rw [cfc_of_diagonalization (unitary_of_mul hV1 hV2) d hdecT f,
    cfc_of_diagonalization (unitary_of_mul hU hU') d hdec f,
    Matrix.transpose_mul, Matrix.transpose_mul, hVH, hdiagT f, Matrix.mul_assoc]

/-- The logarithm of a Kronecker product of positive definite matrices. -/
lemma cfc_log_kron {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    cfc Real.log (A ⊗ₖ B) = (cfc Real.log A) ⊗ₖ (1 : Matrix m m ℂ)
      + (1 : Matrix n n ℂ) ⊗ₖ (cfc Real.log B) := by
  obtain ⟨U, a, hU, hU', hapos, hdA⟩ := exists_diagonalization_pos hA
  obtain ⟨V, b, hV, hV', hbpos, hdB⟩ := exists_diagonalization_pos hB
  have hWH : (U ⊗ₖ V)ᴴ = Uᴴ ⊗ₖ Vᴴ := Matrix.conjTranspose_kronecker U V
  have hW1 : (U ⊗ₖ V) * (U ⊗ₖ V)ᴴ = 1 := by
    rw [hWH, ← Matrix.mul_kronecker_mul, hU, hV, Matrix.one_kronecker_one]
  have hW2 : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [hWH, ← Matrix.mul_kronecker_mul, hU', hV', Matrix.one_kronecker_one]
  have hkron : A ⊗ₖ B = (U ⊗ₖ V) * diagonal (fun p : n × m => ((a p.1 * b p.2 : ℝ) : ℂ))
      * (U ⊗ₖ V)ᴴ := by
    conv_lhs => rw [hdA, hdB]
    rw [hWH, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal]
    congr 2
    funext p
    simp
  rw [cfc_of_diagonalization (unitary_of_mul hW1 hW2) _ hkron Real.log]
  have hsplit : (fun p : n × m => ((Real.log (a p.1 * b p.2) : ℝ) : ℂ))
      = fun p : n × m => ((Real.log (a p.1) : ℝ) : ℂ) * 1 + 1 * ((Real.log (b p.2) : ℝ) : ℂ) := by
    funext p
    rw [Real.log_mul (hapos p.1).ne' (hbpos p.2).ne']
    push_cast
    ring
  rw [hsplit]
  have hdiag : diagonal (fun p : n × m =>
        ((Real.log (a p.1) : ℝ) : ℂ) * 1 + 1 * ((Real.log (b p.2) : ℝ) : ℂ))
      = diagonal (fun i => ((Real.log (a i) : ℝ) : ℂ)) ⊗ₖ (1 : Matrix m m ℂ)
        + (1 : Matrix n n ℂ) ⊗ₖ diagonal (fun j => ((Real.log (b j) : ℝ) : ℂ)) := by
    rw [show (1 : Matrix m m ℂ) = diagonal (fun _ : m => (1 : ℂ)) from by simp,
      show (1 : Matrix n n ℂ) = diagonal (fun _ : n => (1 : ℂ)) from by simp,
      Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal, ← diagonal_add]
  rw [hdiag, Matrix.mul_add, Matrix.add_mul, hWH]
  congr 1
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hV]
    congr 1
    exact (cfc_of_diagonalization (unitary_of_mul hU hU') a hdA Real.log).symm
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hU]
    congr 1
    exact (cfc_of_diagonalization (unitary_of_mul hV hV') b hdB Real.log).symm

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

import RequestProject.Channel
/-!
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Statement: Quantum relative entropy is monotone under CPTP maps (data-processing inequality).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype ι] [DecidableEq ι]

/-! ### The variational functional -/

/-- The functional whose supremum over `Z` is the resolvent quadratic form
`⟪√ρ, (Δ + t)⁻¹ √ρ⟫`. -/
noncomputable def varFun (ρ σ : Matrix n n ℂ) (t : ℝ) (Z : Matrix n n ℂ) : ℝ :=
  2 * (trace (Zᴴ * ρ)).re - (trace (Zᴴ * σ * Z)).re - t * (trace (Zᴴ * Z * ρ)).re

/-- The resolvent quadratic form of the modular operator at the vectorized square root. -/
noncomputable def resolvQuad (ρ σ : Matrix n n ℂ) (t : ℝ) : ℝ :=
  (star (vecm (CFC.sqrt ρ)) ⬝ᵥ
    ((modOp σ ρ + (t : ℂ) • 1)⁻¹ *ᵥ vecm (CFC.sqrt ρ))).re

lemma resolvIntegrand_eq_resolvQuad (ρ σ : Matrix n n ℂ) (hρ : ρ.PosDef) (t : ℝ) :
    resolvIntegrand (modOp σ ρ) (vecm (CFC.sqrt ρ)) t
      = (trace ρ).re * (1/(1+t)) - resolvQuad ρ σ t := by
  rw [resolvIntegrand, resolvQuad, dot_vecm_sqrt_self hρ]

lemma shifted_modOp_posDef {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {t : ℝ} (ht : 0 < t) : (modOp σ ρ + (t : ℂ) • 1).PosDef :=
  (modOp_posDef hσ hρ).add (Matrix.PosDef.one.smul (a := (t : ℂ)) (by exact_mod_cast ht))

/-- `√ρ * ρ⁻¹ * √ρ = 1`. -/
lemma sqrt_mul_inv_mul_sqrt {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    CFC.sqrt ρ * ρ⁻¹ * CFC.sqrt ρ = 1 := by
  set s := CFC.sqrt ρ with hs
  have hsd : s.PosDef := sqrt_posDef hρ
  have hss : s * s = ρ := sqrt_mul_sqrt hρ
  rw [← hss, Matrix.mul_inv_rev,
    show s * (s⁻¹ * s⁻¹) * s = (s * s⁻¹) * (s⁻¹ * s) by simp [Matrix.mul_assoc],
    posDef_mul_inv hsd, posDef_inv_mul hsd, Matrix.one_mul]

/-- The variational functional in vectorized form. -/
lemma varFun_eq_vec {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (t : ℝ) (Z : Matrix n n ℂ) :
    varFun ρ σ t Z
      = 2 * (star (vecm (Z * CFC.sqrt ρ)) ⬝ᵥ vecm (CFC.sqrt ρ)).re
        - (star (vecm (Z * CFC.sqrt ρ)) ⬝ᵥ
            ((modOp σ ρ + (t : ℂ) • 1) *ᵥ vecm (Z * CFC.sqrt ρ))).re := by
  set s := CFC.sqrt ρ with hs
  have hsH : sᴴ = s := sqrt_herm hρ
  have hss : s * s = ρ := sqrt_mul_sqrt hρ
  have hsis : s * ρ⁻¹ * s = 1 := sqrt_mul_inv_mul_sqrt hρ
  have e1 : star (vecm (Z * s)) ⬝ᵥ vecm s = trace (Zᴴ * ρ) := by
    rw [dot_vecm, Matrix.conjTranspose_mul, hsH, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, hss]
  have e2 : (modOp σ ρ + (t : ℂ) • 1) *ᵥ vecm (Z * s)
      = vecm (σ * (Z * s) * ρ⁻¹) + (t : ℂ) • vecm (Z * s) := by
    rw [Matrix.add_mulVec, modOp_mulVec]
    congr 1
    simp [Matrix.smul_mulVec]
  have e3 : star (vecm (Z * s)) ⬝ᵥ vecm (σ * (Z * s) * ρ⁻¹) = trace (Zᴴ * σ * Z) := by
    rw [dot_vecm, Matrix.conjTranspose_mul, hsH]
    calc trace (s * Zᴴ * (σ * (Z * s) * ρ⁻¹))
        = trace ((Zᴴ * σ * Z) * (s * ρ⁻¹ * s)) := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = trace (Zᴴ * σ * Z) := by rw [hsis, Matrix.mul_one]
  have e4 : star (vecm (Z * s)) ⬝ᵥ vecm (Z * s) = trace (Zᴴ * Z * ρ) := by
    rw [dot_vecm, Matrix.conjTranspose_mul, hsH]
    calc trace (s * Zᴴ * (Z * s))
        = trace ((Zᴴ * Z) * (s * s)) := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = trace (Zᴴ * Z * ρ) := by rw [hss]
  rw [e2, dotProduct_add, e1, e3, varFun]
  rw [show star (vecm (Z * s)) ⬝ᵥ ((t : ℂ) • vecm (Z * s))
      = (t : ℂ) * (star (vecm (Z * s)) ⬝ᵥ vecm (Z * s)) by
    rw [dotProduct_smul]; simp [smul_eq_mul]]
  rw [e4]
  simp
  ring

/-- The variational upper bound. -/
theorem varFun_le {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) {t : ℝ} (ht : 0 < t)
    (Z : Matrix n n ℂ) : varFun ρ σ t Z ≤ resolvQuad ρ σ t := by
  rw [varFun_eq_vec hρ t Z, resolvQuad]
  exact variational_le (shifted_modOp_posDef hρ hσ ht) _ _

/-- The variational bound is attained. -/
theorem exists_varFun_eq {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) {t : ℝ}
    (ht : 0 < t) : ∃ Z : Matrix n n ℂ, resolvQuad ρ σ t = varFun ρ σ t Z := by
  set s := CFC.sqrt ρ with hs
  have hsd : s.PosDef := sqrt_posDef hρ
  set S := modOp σ ρ + (t : ℂ) • 1 with hS
  have hSpd : S.PosDef := shifted_modOp_posDef hρ hσ ht
  refine ⟨unvecm (S⁻¹ *ᵥ vecm s) * s⁻¹, ?_⟩
  have hZs : (unvecm (S⁻¹ *ᵥ vecm s) * s⁻¹) * s = unvecm (S⁻¹ *ᵥ vecm s) := by
    rw [Matrix.mul_assoc, posDef_inv_mul hsd, Matrix.mul_one]
  rw [varFun_eq_vec hρ t, hZs, vecm_unvecm, resolvQuad, ← hs, ← hS]
  exact (variational_eq hSpd (vecm s)).symm

/-! ### Behaviour under a channel -/

variable {K : ι → Matrix m n ℂ}

/-- The variational functional decreases along the channel. -/
theorem varFun_channel_le (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {t : ℝ} (ht : 0 ≤ t) (Z : Matrix m m ℂ) :
    varFun (krausMap K ρ) (krausMap K σ) t Z ≤ varFun ρ σ t (krausAdj K Z) := by
  have h1 : (trace (Zᴴ * krausMap K ρ)).re = (trace ((krausAdj K Z)ᴴ * ρ)).re := by
    rw [trace_adj_id]
  have h2 := trace_adj_quad_le hK Z hσ
  have h3 := trace_adj_sq_le hK Z hρ
  rw [varFun, varFun, h1]
  have h3' : t * (trace ((krausAdj K Z)ᴴ * krausAdj K Z * ρ)).re
      ≤ t * (trace (Zᴴ * Z * krausMap K ρ)).re := mul_le_mul_of_nonneg_left h3 ht
  linarith

/-- The resolvent quadratic form decreases along the channel. -/
theorem resolvQuad_channel_le (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hΦρ : (krausMap K ρ).PosDef)
    (hΦσ : (krausMap K σ).PosDef) {t : ℝ} (ht : 0 < t) :
    resolvQuad (krausMap K ρ) (krausMap K σ) t ≤ resolvQuad ρ σ t := by
  obtain ⟨Z, hZ⟩ := exists_varFun_eq hΦρ hΦσ ht
  calc resolvQuad (krausMap K ρ) (krausMap K σ) t
      = varFun (krausMap K ρ) (krausMap K σ) t Z := hZ
    _ ≤ varFun ρ σ t (krausAdj K Z) :=
        varFun_channel_le hK hρ.posSemidef hσ.posSemidef ht.le Z
    _ ≤ resolvQuad ρ σ t := varFun_le hρ hσ ht _

/-! ### The data-processing inequality -/

/-- **Data-processing inequality**: the Umegaki relative entropy
`relEntropy ρ σ = Tr(ρ log ρ) - Tr(ρ log σ)` is monotone under a CPTP map given in
Kraus (operator-sum) form `Φ X = ∑ i, K i * X * (K i)ᴴ` with `∑ i, (K i)ᴴ * (K i) = 1`. -/
theorem data_processing {K : ι → Matrix m n ℂ} (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hΦρ : (krausMap K ρ).PosDef) (hΦσ : (krausMap K σ).PosDef) :
    relEntropy (krausMap K ρ) (krausMap K σ) ≤ relEntropy ρ σ := by
  have htr : trace (krausMap K ρ) = trace ρ := trace_krausMap K hK ρ
  have hint : MeasureTheory.IntegrableOn
      (resolvIntegrand (modOp σ ρ) (vecm (CFC.sqrt ρ))) (Set.Ioi 0) := by
    have hpd := modOp_posDef hσ hρ
    exact integrableOn_resolvIntegrand hpd.isHermitian hpd.eigenvalues_pos _
  have hint' : MeasureTheory.IntegrableOn
      (resolvIntegrand (modOp (krausMap K σ) (krausMap K ρ))
        (vecm (CFC.sqrt (krausMap K ρ)))) (Set.Ioi 0) := by
    have hpd := modOp_posDef hΦσ hΦρ
    exact integrableOn_resolvIntegrand hpd.isHermitian hpd.eigenvalues_pos _
  have hmono : ∀ t ∈ Set.Ioi (0:ℝ),
      resolvIntegrand (modOp σ ρ) (vecm (CFC.sqrt ρ)) t
        ≤ resolvIntegrand (modOp (krausMap K σ) (krausMap K ρ))
            (vecm (CFC.sqrt (krausMap K ρ))) t := by
    intro t ht
    rw [resolvIntegrand_eq_resolvQuad ρ σ hρ t,
      resolvIntegrand_eq_resolvQuad _ _ hΦρ t, htr]
    have := resolvQuad_channel_le hK hρ hσ hΦρ hΦσ ht
    linarith
  rw [relEntropy_eq_neg_integral hρ hσ, relEntropy_eq_neg_integral hΦρ hΦσ, neg_le_neg_iff]
  exact MeasureTheory.setIntegral_mono_on hint hint' measurableSet_Ioi hmono

/-- The identity channel: `krausMap` with a single Kraus operator `1` is the identity.
This witnesses that the hypotheses of `data_processing` are satisfiable. -/
lemma krausMap_one (X : Matrix n n ℂ) :
    krausMap (fun _ : Unit => (1 : Matrix n n ℂ)) X = X := by
  simp [krausMap]

/-- All the hypotheses of `data_processing` are simultaneously satisfiable. -/
example {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    ∃ K : Unit → Matrix n n ℂ, (∑ i, (K i)ᴴ * K i = 1) ∧
      (krausMap K ρ).PosDef ∧ (krausMap K σ).PosDef :=
  ⟨fun _ => 1, by simp, by rw [krausMap_one]; exact hρ, by rw [krausMap_one]; exact hσ⟩

end QI

import RequestProject.Modular

/-!
# Quantum channels in Kraus form

A CPTP map (quantum channel) `Φ : Matrix n n ℂ → Matrix m m ℂ` in operator-sum (Kraus) form,
its adjoint, the Kadison–Schwarz inequality for the unital adjoint, and the trace
inequalities used in the proof of the data-processing inequality.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype ι] [DecidableEq ι]

/-! ### Traces of products of positive matrices -/

/-- The trace of a product of two positive semidefinite matrices is a nonnegative real. -/
lemma trace_mul_nonneg {M N : Matrix n n ℂ} (hM : M.PosSemidef) (hN : N.PosSemidef) :
    0 ≤ (trace (M * N)).re := by
  set s := CFC.sqrt M with hs
  have hss : s * s = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
  have hsps : s.PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have h1 : trace (M * N) = trace (sᴴ * N * s) := by
    rw [hsps.isHermitian, ← hss, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h1]
  have := (hN.conjTranspose_mul_mul_same s).trace_nonneg
  exact_mod_cast Complex.le_def.mp this |>.1

/-! ### Kraus maps -/

/-- A quantum channel in operator-sum (Kraus) form: `Φ X = ∑ i, K i * X * (K i)ᴴ`. -/
noncomputable def krausMap (K : ι → Matrix m n ℂ) (X : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ i, K i * X * (K i)ᴴ

/-- The adjoint (Heisenberg picture) of a Kraus map: `Φ* Z = ∑ i, (K i)ᴴ * Z * K i`. -/
noncomputable def krausAdj (K : ι → Matrix m n ℂ) (Z : Matrix m m ℂ) : Matrix n n ℂ :=
  ∑ i, (K i)ᴴ * Z * K i

omit [Fintype n] [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
lemma krausAdj_conjTranspose (K : ι → Matrix m n ℂ) (Z : Matrix m m ℂ) :
    (krausAdj K Z)ᴴ = krausAdj K Zᴴ := by
  simp only [krausAdj, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
/-- The defining adjunction relation between a Kraus map and its adjoint. -/
lemma trace_krausAdj_mul (K : ι → Matrix m n ℂ) (Z : Matrix m m ℂ) (X : Matrix n n ℂ) :
    trace (krausAdj K Z * X) = trace (Z * krausMap K X) := by
  simp only [krausAdj, krausMap, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (K i)ᴴ * Z * K i * X = (K i)ᴴ * (Z * K i * X) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- Trace preservation. -/
lemma trace_krausMap (K : ι → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix n n ℂ) :
    trace (krausMap K X) = trace X := by
  have h := trace_krausAdj_mul K (1 : Matrix m m ℂ) X
  rw [Matrix.one_mul] at h
  rw [← h]
  simp only [krausAdj, Matrix.mul_one]
  rw [hK, Matrix.one_mul]

omit [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
/-- Positivity: a Kraus map sends positive semidefinite matrices to positive semidefinite
matrices. -/
lemma krausMap_posSemidef (K : ι → Matrix m n ℂ) {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    (krausMap K X).PosSemidef := by
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    (Matrix.PosSemidef.zero) (fun i _ => ?_)
  have := hX.conjTranspose_mul_mul_same (K i)ᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at this

omit [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
/-- Complete positivity: every ampliation `1 ⊗ Φ` of a Kraus map is positive. -/
lemma krausMap_ampliation_posSemidef {p : Type*} [Fintype p] [DecidableEq p]
    (K : ι → Matrix m n ℂ) {X : Matrix (p × n) (p × n) ℂ} (hX : X.PosSemidef) :
    (∑ i, ((1 : Matrix p p ℂ) ⊗ₖ K i) * X * ((1 : Matrix p p ℂ) ⊗ₖ K i)ᴴ).PosSemidef := by
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    (Matrix.PosSemidef.zero) (fun i _ => ?_)
  have := hX.conjTranspose_mul_mul_same (((1 : Matrix p p ℂ) ⊗ₖ K i)ᴴ)
  rwa [Matrix.conjTranspose_conjTranspose] at this

/-! ### The stacked isometry and the Kadison–Schwarz inequality -/

/-- The Kraus operators stacked into a single tall matrix. -/
def stack (K : ι → Matrix m n ℂ) : Matrix (ι × m) n ℂ := Matrix.of fun p b => K p.1 p.2 b

omit [Fintype n] [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
lemma stack_conjTranspose_mul (K : ι → Matrix m n ℂ) :
    (stack K)ᴴ * stack K = ∑ i, (K i)ᴴ * K i := by
  ext b c
  simp [stack, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    Matrix.sum_apply]

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
lemma krausAdj_eq_stack (K : ι → Matrix m n ℂ) (Z : Matrix m m ℂ) :
    krausAdj K Z = (stack K)ᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ Z) * stack K := by
  ext b c
  simp [krausAdj, stack, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.sum_apply, Finset.sum_mul]

/-- **Kadison–Schwarz inequality** for the (unital, completely positive) adjoint of a
trace-preserving Kraus map. -/
theorem kadison_schwarz (K : ι → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (Z : Matrix m m ℂ) :
    (krausAdj K (Zᴴ * Z) - (krausAdj K Zᴴ) * (krausAdj K Z)).PosSemidef := by
  set 𝒦 := stack K with hstack
  have hiso : 𝒦ᴴ * 𝒦 = 1 := by rw [hstack, stack_conjTranspose_mul, hK]
  set P := 𝒦 * 𝒦ᴴ with hP
  have hPH : Pᴴ = P := by rw [hP, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPP : P * P = P := by
    rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc 𝒦ᴴ, hiso, Matrix.one_mul]
  have hQ : ((1 : Matrix (ι × m) (ι × m) ℂ) - P).PosSemidef := by
    have hid : (1 - P) = (1 - P)ᴴ * (1 - P) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hPP]
      abel
    rw [hid]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  set D : Matrix (ι × m) (ι × m) ℂ := (1 : Matrix ι ι ℂ) ⊗ₖ Z with hD
  have hDH : Dᴴ = (1 : Matrix ι ι ℂ) ⊗ₖ Zᴴ := by
    rw [hD, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have hDD : Dᴴ * D = (1 : Matrix ι ι ℂ) ⊗ₖ (Zᴴ * Z) := by
    rw [hDH, hD, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have key : krausAdj K (Zᴴ * Z) - (krausAdj K Zᴴ) * (krausAdj K Z)
      = (D * 𝒦)ᴴ * ((1 : Matrix (ι × m) (ι × m) ℂ) - P) * (D * 𝒦) := by
    rw [krausAdj_eq_stack, krausAdj_eq_stack, krausAdj_eq_stack, ← hstack, ← hD, ← hDH, ← hDD]
    rw [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    congr 1
    · simp only [Matrix.mul_assoc]
    · rw [hP]
      simp only [Matrix.mul_assoc]
  rw [key]
  exact hQ.conjTranspose_mul_mul_same _

/-! ### The three trace estimates -/

variable {K : ι → Matrix m n ℂ}

omit [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
/-- Adjunction identity. -/
lemma trace_adj_id (K : ι → Matrix m n ℂ) (Z : Matrix m m ℂ) (ρ : Matrix n n ℂ) :
    trace ((krausAdj K Z)ᴴ * ρ) = trace (Zᴴ * krausMap K ρ) := by
  rw [krausAdj_conjTranspose, trace_krausAdj_mul]

/-- Contractivity of the adjoint in the `σ`-weighted norm. -/
lemma trace_adj_quad_le (hK : ∑ i, (K i)ᴴ * K i = 1) (Z : Matrix m m ℂ)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    (trace ((krausAdj K Z)ᴴ * σ * (krausAdj K Z))).re
      ≤ (trace (Zᴴ * krausMap K σ * Z)).re := by
  set W := krausAdj K Z with hW
  have hks := kadison_schwarz K hK Zᴴ
  rw [Matrix.conjTranspose_conjTranspose] at hks
  have h1 : (trace (Wᴴ * σ * W)).re = (trace ((krausAdj K Z * krausAdj K Zᴴ) * σ)).re := by
    rw [Matrix.trace_mul_cycle, hW, krausAdj_conjTranspose]
  have h2 : (trace (Zᴴ * krausMap K σ * Z)).re
      = (trace (krausAdj K (Z * Zᴴ) * σ)).re := by
    rw [trace_krausAdj_mul, Matrix.trace_mul_cycle]
  rw [h1, h2, ← sub_nonneg, ← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
  exact trace_mul_nonneg hks hσ

/-- Contractivity of the adjoint in the `ρ`-weighted norm. -/
lemma trace_adj_sq_le (hK : ∑ i, (K i)ᴴ * K i = 1) (Z : Matrix m m ℂ)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (trace ((krausAdj K Z)ᴴ * (krausAdj K Z) * ρ)).re
      ≤ (trace (Zᴴ * Z * krausMap K ρ)).re := by
  have hks := kadison_schwarz K hK Z
  have h1 : (trace ((krausAdj K Z)ᴴ * (krausAdj K Z) * ρ)).re
      = (trace ((krausAdj K Zᴴ * krausAdj K Z) * ρ)).re := by
    rw [krausAdj_conjTranspose]
  have h2 : (trace (Zᴴ * Z * krausMap K ρ)).re
      = (trace (krausAdj K (Zᴴ * Z) * ρ)).re := by
    rw [trace_krausAdj_mul]
  rw [h1, h2, ← sub_nonneg, ← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
  exact trace_mul_nonneg hks hρ

end QI

