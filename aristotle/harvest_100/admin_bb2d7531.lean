import Mathlib
/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

section Rearrangement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Value of the bilinear form `M ↦ ∑ j, ∑ k, M j k * (a j * b k)` at a permutation matrix. -/
lemma sum_permMatrix_mul (a b : ι → ℝ) (σ : Equiv.Perm ι) :
    ∑ j, ∑ k, (σ.permMatrix ℝ) j k * (a j * b k) = ∑ j, a j * b (σ j) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Finset.sum_ite_eq]

/-- Rearrangement inequality over doubly stochastic matrices: if `a` and `b` monovary, the
weighted sum `∑ j k, P j k * (a j * b k)` over a doubly stochastic `P` is at most
`∑ i, a i * b i`. -/
lemma sum_doublyStochastic_le {a b : ι → ℝ} (hab : Monovary a b) {P : Matrix ι ι ℝ}
    (hP : P ∈ doublyStochastic ℝ ι) :
    ∑ j, ∑ k, P j k * (a j * b k) ≤ ∑ i, a i * b i := by
  obtain ⟨w, hw0, hw1, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  have hexp : ∑ j, ∑ k, P j k * (a j * b k)
      = ∑ σ : Equiv.Perm ι, w σ * ∑ j, a j * b (σ j) := by
    calc ∑ j, ∑ k, P j k * (a j * b k)
        = ∑ j, ∑ k, ∑ σ : Equiv.Perm ι, w σ * ((σ.permMatrix ℝ) j k * (a j * b k)) := by
          rw [← hwP]
          simp [Matrix.sum_apply, Finset.sum_mul]
      _ = ∑ j, ∑ σ : Equiv.Perm ι, ∑ k, w σ * ((σ.permMatrix ℝ) j k * (a j * b k)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ σ : Equiv.Perm ι, ∑ j, ∑ k, w σ * ((σ.permMatrix ℝ) j k * (a j * b k)) :=
          Finset.sum_comm
      _ = ∑ σ : Equiv.Perm ι, w σ * ∑ j, ∑ k, (σ.permMatrix ℝ) j k * (a j * b k) := by
          simp [Finset.mul_sum]
      _ = ∑ σ : Equiv.Perm ι, w σ * ∑ j, a j * b (σ j) := by
          simp
  rw [hexp]
  calc ∑ σ : Equiv.Perm ι, w σ * ∑ j, a j * b (σ j)
      ≤ ∑ _σ : Equiv.Perm ι, w _σ * ∑ i, a i * b i := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have h : ∑ j, a j * b (σ j) ≤ ∑ i, a i * b i :=
          hab.sum_smul_comp_perm_le_sum_smul
        exact mul_le_mul_of_nonneg_left h (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- Two antitone functions on a linearly ordered index type monovary. -/
lemma Monovary.of_antitone {a b : ι → ℝ} [LinearOrder ι] (ha : Antitone a) (hb : Antitone b) :
    Monovary a b := by
  intro i j hij
  rcases le_total j i with h | h
  · exact ha h
  · exact absurd (hb h) (not_le.2 hij)

end Rearrangement

section Weights

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {A B : Matrix n n 𝕜}

/-- The unitary `W = U⋆ V` relating the eigenvector bases of `A` and `B`. -/
noncomputable def eigTransition (hA : A.IsHermitian) (hB : B.IsHermitian) : Matrix n n 𝕜 :=
  (star (hA.eigenvectorUnitary : Matrix n n 𝕜)) * (hB.eigenvectorUnitary : Matrix n n 𝕜)

lemma eigTransition_star_mul (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (star (eigTransition hA hB)) * eigTransition hA hB = 1 := by
  have hU : (hA.eigenvectorUnitary : Matrix n n 𝕜) * star (hA.eigenvectorUnitary : Matrix n n 𝕜)
      = 1 := mul_eq_one_comm.mp (UnitaryGroup.star_mul_self _)
  have hV : star (hB.eigenvectorUnitary : Matrix n n 𝕜) * (hB.eigenvectorUnitary : Matrix n n 𝕜)
      = 1 := UnitaryGroup.star_mul_self _
  simp only [eigTransition, Matrix.star_mul, star_star]
  rw [mul_assoc, ← mul_assoc (hA.eigenvectorUnitary : Matrix n n 𝕜), hU, one_mul, hV]

lemma eigTransition_mul_star (hA : A.IsHermitian) (hB : B.IsHermitian) :
    eigTransition hA hB * (star (eigTransition hA hB)) = 1 :=
  mul_eq_one_comm.mp (eigTransition_star_mul hA hB)

/-- The weight matrix `|W_{jk}|²` of the transition unitary. -/
noncomputable def eigWeight (hA : A.IsHermitian) (hB : B.IsHermitian) : Matrix n n ℝ :=
  Matrix.of fun j k => ‖eigTransition hA hB j k‖ ^ 2

/-- Row sums of `|W_{jk}|²` for a matrix `W` with `W * W⋆ = 1`. -/
lemma sum_normSq_row (W : Matrix n n 𝕜) (h : W * star W = 1) (j : n) :
    ∑ k, ‖W j k‖ ^ 2 = 1 := by
  have hc : ((∑ k, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [RCLike.ofReal_sum]
    calc ∑ k, ((‖W j k‖ ^ 2 : ℝ) : 𝕜) = ∑ k, W j k * (star W) k j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.star_apply, RCLike.star_def, RCLike.mul_conj]
          push_cast
          ring
      _ = (W * star W) j j := Matrix.mul_apply.symm
      _ = 1 := by rw [h]; simp
  exact_mod_cast hc

/-- Column sums of `|W_{jk}|²` for a matrix `W` with `W⋆ * W = 1`. -/
lemma sum_normSq_col (W : Matrix n n 𝕜) (h : star W * W = 1) (k : n) :
    ∑ j, ‖W j k‖ ^ 2 = 1 := by
  have hc : ((∑ j, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [RCLike.ofReal_sum]
    calc ∑ j, ((‖W j k‖ ^ 2 : ℝ) : 𝕜) = ∑ j, (star W) k j * W j k := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.star_apply, RCLike.star_def, RCLike.conj_mul]
          push_cast
          ring
      _ = (star W * W) k k := Matrix.mul_apply.symm
      _ = 1 := by rw [h]; simp
  exact_mod_cast hc

lemma eigWeight_mem_doublyStochastic (hA : A.IsHermitian) (hB : B.IsHermitian) :
    eigWeight hA hB ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · exact sum_normSq_row _ (eigTransition_mul_star hA hB) i
  · exact sum_normSq_col _ (eigTransition_star_mul hA hB) j

/-- Entrywise form of the spectral theorem. -/
lemma hermitian_entry (hA : A.IsHermitian) (i j : n) :
    A i j = ∑ k, ((hA.eigenvalues k : 𝕜)) *
      ((hA.eigenvectorUnitary : Matrix n n 𝕜) i k *
        (starRingEnd 𝕜) ((hA.eigenvectorUnitary : Matrix n n 𝕜) j k)) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    RCLike.star_def, mul_comm, mul_assoc, mul_left_comm]

/-- `tr (A * B) = ∑_{jk} |W_{jk}|² a_j b_k`, in particular it is real. -/
lemma trace_mul_eq_ofReal (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace
      = ((∑ j, ∑ k, eigWeight hA hB j k * (hA.eigenvalues j * hB.eigenvalues k) : ℝ) : 𝕜) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hV
  set a : n → ℝ := hA.eigenvalues with ha
  set b : n → ℝ := hB.eigenvalues with hb
  set f : n → n → n → n → 𝕜 := fun i j k l =>
    ((a k : 𝕜) * (U i k * (starRingEnd 𝕜) (U j k))) *
      ((b l : 𝕜) * (V j l * (starRingEnd 𝕜) (V i l))) with hf
  have hreorder : ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
    rw [show (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ p : n × n, ∑ q : n × n, f p.1 p.2 q.1 q.2 by
         simp [Fintype.sum_prod_type],
       show (∑ k, ∑ l, ∑ i, ∑ j, f i j k l) = ∑ q : n × n, ∑ p : n × n, f p.1 p.2 q.1 q.2 by
         simp [Fintype.sum_prod_type]]
    exact Finset.sum_comm
  have hlhs : (A * B).trace = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := by
    have h1 : (A * B).trace = ∑ i, ∑ j, A i j * B j i := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hermitian_entry hA i j, hermitian_entry hB j i, Finset.sum_mul_sum]
  have hrhs : ((∑ j, ∑ k, eigWeight hA hB j k * (a j * b k) : ℝ) : 𝕜)
      = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
    simp only [RCLike.ofReal_sum, RCLike.ofReal_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hW : ((eigWeight hA hB k l : ℝ) : 𝕜)
        = (starRingEnd 𝕜) (eigTransition hA hB k l) * (eigTransition hA hB k l) := by
      rw [RCLike.conj_mul]
      simp [eigWeight]
    have hWkl : eigTransition hA hB k l = ∑ j, (starRingEnd 𝕜) (U j k) * V j l := by
      simp [eigTransition, Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, hU, hV]
    have hWc : (starRingEnd 𝕜) (eigTransition hA hB k l)
        = ∑ i, U i k * (starRingEnd 𝕜) (V i l) := by
      rw [hWkl, map_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
    rw [hW, hWc, hWkl, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf]
    ring
  rw [hlhs, hreorder, ← hrhs]

/-- `Re tr (A * B) = ∑_{jk} |W_{jk}|² a_j b_k`. -/
lemma re_trace_mul_eq (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re ((A * B).trace)
      = ∑ j, ∑ k, eigWeight hA hB j k * (hA.eigenvalues j * hB.eigenvalues k) := by
  rw [trace_mul_eq_ofReal hA hB, RCLike.ofReal_re]

end Weights

/-- **Von Neumann trace inequality, Hermitian case.**
For Hermitian matrices `A`, `B` over an `RCLike` field indexed by a finite type,
the real part of `tr (A * B)` is at most the sum of the products of their eigenvalues,
each family sorted in decreasing order (`Matrix.IsHermitian.eigenvalues₀`). -/
theorem vonNeumann_trace_ineq_hermitian {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re ((A * B).trace) ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  classical
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  have hev : ∀ (C : Matrix n n 𝕜) (hC : C.IsHermitian) (i : Fin (Fintype.card n)),
      hC.eigenvalues (e i) = hC.eigenvalues₀ i := by
    intro C hC i
    simp [Matrix.IsHermitian.eigenvalues, he]
  -- the reindexed weight matrix is doubly stochastic
  have hQ : (Matrix.reindex e.symm e.symm (eigWeight hA hB)) ∈
      doublyStochastic ℝ (Fin (Fintype.card n)) :=
    reindex_mem_doublyStochastic (eigWeight_mem_doublyStochastic hA hB)
  have hmono : Monovary hA.eigenvalues₀ hB.eigenvalues₀ :=
    Monovary.of_antitone hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone
  have hkey := sum_doublyStochastic_le hmono hQ
  rw [re_trace_mul_eq hA hB]
  refine le_trans (le_of_eq ?_) hkey
  rw [← Equiv.sum_comp e (fun j => ∑ k, eigWeight hA hB j k *
    (hA.eigenvalues j * hB.eigenvalues k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Equiv.sum_comp e (fun k => eigWeight hA hB (e j) k *
    (hA.eigenvalues (e j) * hB.eigenvalues k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hev A hA j, hev B hB k]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

end Zeta23Core

