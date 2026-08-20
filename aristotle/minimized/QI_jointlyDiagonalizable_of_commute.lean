import Mathlib
import RequestProject.Holevo

/-!
# Simultaneous diagonalization of a commuting family of Hermitian matrices

The main result `QI.jointlyDiagonalizable_of_commute` shows that a family of pairwise commuting
Hermitian matrices is diagonal in a common orthonormal basis, i.e. satisfies
`QI.JointlyDiagonalizable`.
-/

open Matrix LinearMap
open scoped Function

namespace QI

variable {n X : Type*} [Fintype n] [DecidableEq n]

theorem jointlyDiagonalizable_of_commute (ρ : X → Matrix n n ℂ)
    (hherm : ∀ x, (ρ x).IsHermitian) (hcomm : ∀ x x', Commute (ρ x) (ρ x')) :
    JointlyDiagonalizable ρ := by
  classical
  -- pass to linear maps on Euclidean space
  set T : X → Module.End ℂ (EuclideanSpace ℂ n) := fun x => Matrix.toEuclideanLin (ρ x) with hTdef
  have hmul : ∀ (C D : Matrix n n ℂ), Matrix.toEuclideanLin C * Matrix.toEuclideanLin D
      = Matrix.toEuclideanLin (C * D) := by
    intro C D
    ext v i
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hT : ∀ x, (T x).IsSymmetric := fun x => Matrix.isHermitian_iff_isSymmetric.1 (hherm x)
  have hC : Pairwise (Commute on T) := by
    intro x x' _
    show T x * T x' = T x' * T x
    rw [hTdef]; simp only
    rw [hmul, hmul, (hcomm x x').eq]
  -- the joint eigenspaces decompose the space
  have hint := LinearMap.IsSymmetric.LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute
    hT hC
  set V : (X → ℂ) → Submodule ℂ (EuclideanSpace ℂ n) :=
    fun α => ⨅ x, (T x).eigenspace (α x) with hV
  have hOF := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  set bas := hint.collectedBasis (fun α => (stdOrthonormalBasis ℂ (V α)).toBasis) with hbas
  haveI : Fintype ((α : X → ℂ) × Fin (Module.finrank ℂ (V α))) :=
    FiniteDimensional.fintypeBasisIndex bas
  have horth : Orthonormal ℂ bas := by
    simpa [hbas] using hOF.orthonormal_sigma_orthonormal
      (show ∀ α, Orthonormal ℂ (stdOrthonormalBasis ℂ (V α)).toBasis by simp)
  set ob := bas.toOrthonormalBasis horth with hob
  have hobcoe : ⇑ob = ⇑bas := Module.Basis.coe_toOrthonormalBasis _ _
  have hmem : ∀ a, ob a ∈ V a.1 := by
    intro a
    rw [hobcoe]
    exact hint.collectedBasis_mem (fun α => (stdOrthonormalBasis ℂ (V α)).toBasis) a
  -- reindex the basis by `n`
  have hcard : Fintype.card ((α : X → ℂ) × Fin (Module.finrank ℂ (V α))) = Fintype.card n := by
    have h1 := Module.finrank_eq_card_basis bas
    have h2 : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace
    omega
  set e := Fintype.equivOfCardEq hcard with he
  set b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := ob.reindex e with hbdef
  have hbmem : ∀ i : n, b i ∈ V (e.symm i).1 := by
    intro i
    rw [hbdef, OrthonormalBasis.reindex_apply]
    exact hmem _
  -- the eigenvalues are real
  have heig : ∀ (i : n) (x : X), T x (b i) = ((e.symm i).1 x) • b i := by
    intro i x
    have h : b i ∈ ⨅ x, (T x).eigenspace ((e.symm i).1 x) := hbmem i
    rw [Submodule.mem_iInf] at h
    exact (Module.End.mem_eigenspace_iff).1 (h x)
  have hbne : ∀ i : n, b i ≠ 0 := by
    intro i h
    have := b.orthonormal.1 i
    rw [h] at this
    simp at this
  have hreal : ∀ (i : n) (x : X), (((e.symm i).1 x).re : ℂ) = (e.symm i).1 x := by
    intro i x
    have hev : Module.End.HasEigenvalue (T x) ((e.symm i).1 x) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨(Module.End.mem_eigenspace_iff).2 (heig i x),
        hbne i⟩
    have := (hT x).conj_eigenvalue_eq_self hev
    exact Complex.conj_eq_iff_re.1 this
  set v : X → n → ℝ := fun x i => ((e.symm i).1 x).re with hvdef
  -- the unitary whose columns are the joint eigenvectors
  set U : Matrix n n ℂ := (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix ⇑b with hUdef
  have hUmem : U ∈ Matrix.unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hUapply : ∀ i j : n, U i j = (b j) i := fun _ _ => rfl
  have hUcol : ∀ j : n, U *ᵥ Pi.single j 1 = ⇑(b j) := by
    intro j
    rw [Matrix.mulVec_single_one]
    rfl
  -- the eigenvector equation in matrix form
  have hmulVec : ∀ (x : X) (j : n), ρ x *ᵥ ⇑(b j) = (v x j : ℂ) • ⇑(b j) := by
    intro x j
    have h := heig j x
    rw [hTdef] at h
    simp only [Matrix.toLpLin_apply] at h
    have h2 := congrArg (fun w : EuclideanSpace ℂ n => WithLp.ofLp w) h
    simpa [hvdef, hreal j x] using h2
  refine ⟨U, hUmem, fun x => ⟨v x, ?_⟩⟩
  have hUU : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := U)).1 hUmem
    simpa using this
  have hkey : ρ x * U = U * Matrix.diagonal (fun i => (v x i : ℂ)) := by
    ext i j
    have hL : (ρ x * U) *ᵥ Pi.single j 1 = (v x j : ℂ) • ⇑(b j) := by
      rw [← Matrix.mulVec_mulVec, hUcol j, hmulVec x j]
    have hR : (U * Matrix.diagonal (fun i => (v x i : ℂ))) *ᵥ Pi.single j 1
        = (v x j : ℂ) • ⇑(b j) := by
      rw [← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single, mul_one]
      have hs : (Pi.single j ((v x j : ℂ)) : n → ℂ)
          = (v x j : ℂ) • (Pi.single j 1 : n → ℂ) := by
        ext k
        by_cases hk : k = j <;> simp [Pi.single_apply, hk]
      rw [hs, mulVec_smul, hUcol j]
    have := hL.trans hR.symm
    have hcol := congrFun this i
    simpa [Matrix.mulVec_single_one] using hcol
  calc ρ x = ρ x * (U * Uᴴ) := by rw [hUU, mul_one]
    _ = (ρ x * U) * Uᴴ := by rw [mul_assoc]
    _ = U * Matrix.diagonal (fun i => (v x i : ℂ)) * Uᴴ := by rw [hkey]

/-! ### The Holevo bound for commuting ensembles -/

variable {Y : Type*} [Fintype X] [Fintype Y]

/-- The mutual information obtained from any POVM measurement on an ensemble of pairwise
commuting states is at most the Holevo χ quantity of the ensemble. -/

noncomputable def outcomeProb (ρ E : Matrix n n ℂ) : ℝ := (ρ * E).trace.re

/-- The Holevo χ quantity of an ensemble. -/

noncomputable def measInfo (p : X → ℝ) (ρ : X → Matrix n n ℂ) (E : Y → Matrix n n ℂ) : ℝ :=
  shannonEntropy (fun y => ∑ x, p x * outcomeProb (ρ x) (E y))
    - ∑ x, p x * shannonEntropy (fun y => outcomeProb (ρ x) (E y))

/-- The accessible information of an ensemble: the supremum of the mutual information over all
POVMs (with an arbitrary finite number of outcomes). -/

def JointlyDiagonalizable (ρ : X → Matrix n n ℂ) : Prop :=
  ∃ U : Matrix n n ℂ, U ∈ Matrix.unitaryGroup n ℂ ∧
    ∀ x, ∃ v : n → ℝ, ρ x = U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ

omit [Fintype X] in
/-- A jointly diagonalizable family of states is a commuting family. For the converse, see
`QI.jointlyDiagonalizable_of_commute`. -/

lemma JointlyDiagonalizable.commute {ρ : X → Matrix n n ℂ} (h : JointlyDiagonalizable ρ)
    (x x' : X) : Commute (ρ x) (ρ x') := by
  obtain ⟨U, hU, hv⟩ := h
  obtain ⟨v, hvx⟩ := hv x
  obtain ⟨w, hwx⟩ := hv x'
  have hUU : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (A := U)).1 hU
  have hdd : Matrix.diagonal (fun i => (v i : ℂ)) * Matrix.diagonal (fun i => (w i : ℂ))
      = Matrix.diagonal (fun i => (w i : ℂ)) * Matrix.diagonal (fun i => (v i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact Matrix.diagonal_eq_diagonal_iff.2 fun i => by ring
  show ρ x * ρ x' = ρ x' * ρ x
  rw [hvx, hwx]
  calc U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ *
        (U * Matrix.diagonal (fun i => (w i : ℂ)) * Uᴴ)
      = U * (Matrix.diagonal (fun i => (v i : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun i => (w i : ℂ))) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal (fun i => (w i : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun i => (v i : ℂ))) * Uᴴ := by
        rw [hUU, mul_one, mul_one, hdd]
    _ = U * Matrix.diagonal (fun i => (w i : ℂ)) * Uᴴ *
          (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ) := by
        simp only [Matrix.mul_assoc]

/-! ### A sanity check: perfectly distinguishable states -/

/-- Measuring the ensemble `{(1/2, |0⟩⟨0|), (1/2, |1⟩⟨1|)}` in the computational basis yields
one nat (`log 2`) of information; in particular the definitions above are not degenerate. -/
example :
    measInfo (n := Fin 2) (X := Fin 2) (Y := Fin 2) (fun _ => 1 / 2)
      (fun x => Matrix.diagonal (fun i => if i = x then (1 : ℂ) else 0))
      (fun y => Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0)) = Real.log 2 := by
  have hprob : ∀ x y : Fin 2,
      outcomeProb (Matrix.diagonal (fun i => if i = x then (1 : ℂ) else 0))
        (Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0)) = if x = y then 1 else 0 := by
    intro x y
    rw [outcomeProb, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    by_cases h : x = y <;> simp [h, Fin.sum_univ_two, Fin.ext_iff] <;>
      fin_cases x <;> fin_cases y <;> simp_all
  rw [measInfo]
  simp only [hprob]
  rw [shannonEntropy]
  have h1 : ∀ y : Fin 2, (∑ x : Fin 2, (1 / 2 : ℝ) * (if x = y then 1 else 0)) = 1 / 2 := by
    intro y; fin_cases y <;> simp
  simp only [h1]
  have h2 : ∀ x : Fin 2, shannonEntropy (fun y : Fin 2 => if x = y then (1 : ℝ) else 0) = 0 := by
    intro x
    rw [shannonEntropy]
    fin_cases x <;> simp [Fin.sum_univ_two]
  simp only [h2]
  simp [Real.negMulLog, Real.log_inv]

/-! ### Elementary matrix facts -/

noncomputable def shannonEntropy (P : Y → ℝ) : ℝ := ∑ y, Real.negMulLog (P y)

/-- Kullback-Leibler divergence of two finite nonnegative vectors, using the convention
`Real.log 0 = 0`. -/
