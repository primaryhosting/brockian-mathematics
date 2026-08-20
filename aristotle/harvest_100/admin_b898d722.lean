/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Core

open Matrix Finset

section Weights

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise squared-modulus matrix `j k ↦ ‖W j k‖ ^ 2` of a matrix `W`. -/
noncomputable def sqAbsMatrix (W : Matrix n n 𝕜) : Matrix n n ℝ :=
  Matrix.of fun j k => ‖W j k‖ ^ 2

omit [Fintype n] [DecidableEq n] in
@[simp] lemma sqAbsMatrix_apply (W : Matrix n n 𝕜) (j k : n) :
    sqAbsMatrix W j k = ‖W j k‖ ^ 2 := rfl

/-- If `W` is unitary, its entrywise squared-modulus matrix is doubly stochastic. -/
lemma sqAbsMatrix_mem_doublyStochastic {W : Matrix n n 𝕜} (h1 : W * star W = 1)
    (h2 : star W * W = 1) : sqAbsMatrix W ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun j k => by simp, fun j => ?_, fun k => ?_⟩
  · have hj := congrFun (congrFun h1 j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at hj
    have : ((∑ k, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      rw [← hj]
      exact Finset.sum_congr rfl fun k _ => (RCLike.mul_conj (W j k)).symm
    simpa using (by exact_mod_cast this : (∑ k, ‖W j k‖ ^ 2 : ℝ) = 1)
  · have hk := congrFun (congrFun h2 k) k
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at hk
    have : ((∑ j, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      rw [← hk]
      exact Finset.sum_congr rfl fun j _ => (RCLike.conj_mul (W j k)).symm
    simpa using (by exact_mod_cast this : (∑ j, ‖W j k‖ ^ 2 : ℝ) = 1)

end Weights

section Rearrangement

variable {N : Type*} [Fintype N] [DecidableEq N] [LinearOrder N]

/-- For a doubly stochastic weight matrix `S` and antitone `a`, `b`, the weighted sum
`∑ j k, a j * b k * S j k` is at most the aligned sum `∑ i, a i * b i`. -/
lemma sum_mul_weight_le_of_mem_doublyStochastic {a b : N → ℝ} (ha : Antitone a) (hb : Antitone b)
    {S : Matrix N N ℝ} (hS : S ∈ doublyStochastic ℝ N) :
    ∑ j, ∑ k, a j * b k * S j k ≤ ∑ i, a i * b i := by
  obtain ⟨w, hw0, hw1, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hperm : ∀ (σ : Equiv.Perm N) (j : N), ∑ k, b k * (σ.permMatrix ℝ j k) = b (σ j) := by
    intro σ j
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hSjk : ∀ j k, S j k = ∑ σ : Equiv.Perm N, w σ * (σ.permMatrix ℝ j k) := by
    intro j k
    rw [← hw]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 : ∀ j, ∑ k, a j * b k * S j k = ∑ σ : Equiv.Perm N, w σ * (a j * b (σ j)) := by
    intro j
    simp_rw [hSjk, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h : ∀ k, a j * b k * (w σ * (σ.permMatrix ℝ j k))
        = (w σ * a j) * (b k * (σ.permMatrix ℝ j k)) := fun k => by ring
    simp_rw [h, ← Finset.mul_sum, hperm σ j]
    ring
  calc ∑ j, ∑ k, a j * b k * S j k
      = ∑ σ : Equiv.Perm N, w σ * ∑ j, a j * b (σ j) := by
        simp_rw [h1, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ σ : Equiv.Perm N, w σ * ∑ j, a j * b j :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left ((ha.monovary hb).sum_mul_comp_perm_le_sum_mul) (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

end Rearrangement

section Trace

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of `diagonal a * (W * diagonal b * Wᴴ)` in terms of the squared moduli of `W`. -/
lemma trace_diagonal_conj (a b : n → ℝ) (W : Matrix n n 𝕜) :
    (Matrix.diagonal ((RCLike.ofReal ∘ a : n → 𝕜)) *
        (W * Matrix.diagonal ((RCLike.ofReal ∘ b : n → 𝕜)) * star W)).trace
      = ((∑ j, ∑ k, a j * b k * ‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
  have hdiag : ∀ j : n,
      (W * Matrix.diagonal ((RCLike.ofReal ∘ b : n → 𝕜)) * star W : Matrix n n 𝕜) j j
        = ∑ k, ((b k : 𝕜)) * ((‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
    intro j
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, RCLike.star_def,
      Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (W j k) ((b k : 𝕜)), mul_assoc, RCLike.mul_conj]
    push_cast
    ring
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Function.comp_apply, hdiag]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- With `A = U diag(a) U⋆` and `B = V diag(b) V⋆` Hermitian, the trace of `A * B` equals
`∑ j k, a j * b k * ‖W j k‖ ^ 2` where `W = U⋆ V`. -/
lemma trace_mul_eq_sum {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace =
      ((∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k *
        ‖((star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
          (hB.eigenvectorUnitary : Matrix n n 𝕜)) j k)‖ ^ 2 : ℝ) : 𝕜) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hV
  set Da : Matrix n n 𝕜 := Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues : n → 𝕜)) with hDa
  set Db : Matrix n n 𝕜 := Matrix.diagonal ((RCLike.ofReal ∘ hB.eigenvalues : n → 𝕜)) with hDb
  have hstarW : star (star U * V) = star V * U := by
    rw [Matrix.star_mul, star_star]
  have e1 : A * B = U * (Da * (star U * V * Db * star V)) := by
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    noncomm_ring
  have e2 : (A * B).trace = (Da * ((star U * V) * Db * star (star U * V))).trace := by
    rw [e1, Matrix.trace_mul_comm, hstarW]
    congr 1
    noncomm_ring
  rw [e2, trace_diagonal_conj hA.eigenvalues hB.eigenvalues (star U * V)]

end Trace

/-- **Von Neumann trace inequality, Hermitian case.**
For Hermitian matrices `A`, `B` over an `RCLike` field indexed by a finite type,
the real part of `trace (A * B)` is at most `∑ i, a i * b i`, where `a` and `b` are the
eigenvalues of `A` and `B` listed in decreasing order (`Matrix.IsHermitian.eigenvalues₀`,
which is antitone by `Matrix.IsHermitian.eigenvalues₀_antitone`). -/
theorem vonNeumann_trace_ineq_hermitian {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hV
  set W : Matrix n n 𝕜 := star U * V with hW
  have hUsU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  have hUUs : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hVsV : star V * V = 1 := Matrix.UnitaryGroup.star_mul_self hB.eigenvectorUnitary
  have hVVs : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hB.eigenvectorUnitary.2
  have hstarW : star W = star V * U := by rw [hW, Matrix.star_mul, star_star]
  have hWWs : W * star W = 1 := by
    rw [hW, hstarW, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVVs, Matrix.one_mul, hUsU]
  have hWsW : star W * W = 1 := by
    rw [hW, hstarW, Matrix.mul_assoc, ← Matrix.mul_assoc U, hUUs, Matrix.one_mul, hVsV]
  have hds : sqAbsMatrix W ∈ doublyStochastic ℝ n := sqAbsMatrix_mem_doublyStochastic hWWs hWsW
  set E : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
    with hE
  have hare : ∀ i, hA.eigenvalues (E i) = hA.eigenvalues₀ i := by
    intro i; simp [hE, Matrix.IsHermitian.eigenvalues]
  have hbre : ∀ i, hB.eigenvalues (E i) = hB.eigenvalues₀ i := by
    intro i; simp [hE, Matrix.IsHermitian.eigenvalues]
  rw [trace_mul_eq_sum hA hB, RCLike.ofReal_re]
  have hreindex : ∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k * sqAbsMatrix W j k
      = ∑ i, ∑ i', hA.eigenvalues₀ i * hB.eigenvalues₀ i' *
          ((sqAbsMatrix W).reindex E.symm E.symm) i i' := by
    rw [← Equiv.sum_comp E (fun j => ∑ k, hA.eigenvalues j * hB.eigenvalues k * sqAbsMatrix W j k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp E
      (fun k => hA.eigenvalues (E i) * hB.eigenvalues k * sqAbsMatrix W (E i) k)]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp [hare, hbre]
  calc (∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k * ‖W j k‖ ^ 2)
      = ∑ i, ∑ i', hA.eigenvalues₀ i * hB.eigenvalues₀ i' *
          ((sqAbsMatrix W).reindex E.symm E.symm) i i' := hreindex
    _ ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i :=
        sum_mul_weight_le_of_mem_doublyStochastic hA.eigenvalues₀_antitone
          hB.eigenvalues₀_antitone (reindex_mem_doublyStochastic hds)

end Zeta23Core

