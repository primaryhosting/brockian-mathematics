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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

section DoublyStochastic

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Two antitone functions monovary. -/
theorem monovary_of_antitone [LinearOrder n] {a b : n → ℝ} (ha : Antitone a) (hb : Antitone b) :
    Monovary a b := by
  intro i j hij
  rcases le_total i j with h | h
  · exact absurd (hb h) (not_le.mpr hij)
  · exact ha h

/-- If `D` is doubly stochastic and `a`, `b` monovary, then the "weighted pairing"
`∑ j k, D j k * (a j * b k)` is at most the aligned pairing `∑ i, a i * b i`.
This is the combinatorial heart of the von Neumann trace inequality, proved via Birkhoff's
theorem together with the rearrangement inequality. -/
theorem sum_mul_le_of_mem_doublyStochastic {a b : n → ℝ} (hab : Monovary a b)
    {D : Matrix n n ℝ} (hD : D ∈ doublyStochastic ℝ n) :
    ∑ j, ∑ k, D j k * (a j * b k) ≤ ∑ i, a i * b i := by
  have hlin : IsLinearMap ℝ (fun M : Matrix n n ℝ => ∑ j, ∑ k, M j k * (a j * b k)) := by
    constructor
    · intro M N
      simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    · intro c M
      simp [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hmem : D ∈ {M : Matrix n n ℝ |
      (fun M : Matrix n n ℝ => ∑ j, ∑ k, M j k * (a j * b k)) M ≤ ∑ i, a i * b i} := by
    rw [← SetLike.mem_coe, doublyStochastic_eq_convexHull_permMatrix] at hD
    refine convexHull_min ?_ (convex_halfSpace_le hlin _) hD
    rintro _ ⟨σ, rfl⟩
    simp only [Set.mem_setOf_eq]
    have key : ∀ j : n, ∑ k, (σ.permMatrix ℝ) j k * (a j * b k) = a j • b (σ j) := by
      intro j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv, smul_eq_mul]
    rw [Finset.sum_congr rfl fun j _ => key j]
    exact hab.sum_smul_comp_perm_le_sum_smul
  exact hmem

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/
theorem sq_norm_mem_doublyStochastic {𝕜 : Type*} [RCLike 𝕜] (W : Matrix n n 𝕜)
    (hW1 : W * star W = 1) (hW2 : star W * W = 1) :
    (fun j k => ‖W j k‖ ^ 2 : Matrix n n ℝ) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by positivity, fun j => ?_, fun k => ?_⟩
  · have h := congrFun (congrFun hW1 j) j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at h
    have h' : (RCLike.ofReal (∑ k, ‖W j k‖ ^ 2) : 𝕜) = 1 := by
      rw [← h]; push_cast
      exact Finset.sum_congr rfl fun k _ => (RCLike.mul_conj _).symm
    exact_mod_cast h'
  · have h := congrFun (congrFun hW2 k) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at h
    have h' : (RCLike.ofReal (∑ j, ‖W j k‖ ^ 2) : 𝕜) = 1 := by
      rw [← h]; push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      exact (RCLike.mul_conj _).symm
    exact_mod_cast h'

end DoublyStochastic

section Trace

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of `diag(α) * W * diag(β) * Wᴴ` in terms of the squared absolute values of the
entries of `W`. -/
theorem trace_diagonal_mul_mul_diagonal_mul_star (α β : n → ℝ) (W : Matrix n n 𝕜) :
    trace (diagonal (RCLike.ofReal ∘ α) * W * (diagonal (RCLike.ofReal ∘ β) * star W))
      = RCLike.ofReal (∑ j, ∑ k, α j * β k * ‖W j k‖ ^ 2) := by
  rw [trace]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [diag_apply, Matrix.mul_apply, diagonal_apply, Matrix.star_apply,
    Function.comp_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : W j k * (starRingEnd 𝕜) (W j k) = (‖W j k‖ : 𝕜) ^ 2 := RCLike.mul_conj _
  rw [RCLike.star_def]
  linear_combination (RCLike.ofReal (α j) * RCLike.ofReal (β k) : 𝕜) * h

/-- For Hermitian `A`, `B` with eigenvalue lists `α`, `β`, the trace of `A * B` equals
`∑ j k, α j * β k * |W j k|²` for the unitary `W = Uᴴ V` built from the eigenvector
unitaries of `A` and `B`. -/
theorem trace_mul_eq_sum_sq_norm {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ W : Matrix n n 𝕜, W * star W = 1 ∧ star W * W = 1 ∧
      trace (A * B) =
        RCLike.ofReal (∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k * ‖W j k‖ ^ 2) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  have hU1 : U * star U = 1 := by
    rw [hUdef]; exact_mod_cast Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hU2 : star U * U = 1 := by
    rw [hUdef]; exact_mod_cast Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hV1 : V * star V = 1 := by
    rw [hVdef]; exact_mod_cast Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hV2 : star V * V = 1 := by
    rw [hVdef]; exact_mod_cast Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  set Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDa
  set Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hB.eigenvalues) with hDb
  have hAeq : A = U * Da * star U := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hBeq : B = V * Db * star V := by
    conv_lhs => rw [hB.spectral_theorem, Unitary.conjStarAlgAut_apply]
  refine ⟨star U * V, ?_, ?_, ?_⟩
  · rw [Matrix.star_mul, star_star]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by
          simp only [mul_assoc]
      _ = 1 := by rw [hV1, mul_one, hU2]
  · calc star (star U * V) * (star U * V) = star V * (U * star U) * V := by
          rw [Matrix.star_mul, star_star]; simp only [mul_assoc]
      _ = 1 := by rw [hU1, mul_one, hV2]
  · rw [← trace_diagonal_mul_mul_diagonal_mul_star]
    have hstar : star (star U * V) = star V * U := by rw [Matrix.star_mul, star_star]
    rw [hstar, ← hDa, ← hDb]
    have hconj : U * (Da * (star U * V) * (Db * (star V * U))) * star U = A * B := by
      rw [hAeq, hBeq]
      simp only [mul_assoc, hU1, mul_one]
    rw [← hconj]
    rw [mul_assoc, trace_mul_comm]
    simp only [mul_assoc, hU2, mul_one]

end Trace

section Sorted

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The eigenvalues of a Hermitian matrix indexed by `Fin n`, listed in decreasing order. -/
noncomputable def sortedEigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) : Fin n → ℝ :=
  hA.eigenvalues ∘ Tuple.sort (fun i => -(hA.eigenvalues i))

theorem sortedEigenvalues_eq_comp {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    sortedEigenvalues hA = hA.eigenvalues ∘ Tuple.sort (fun i => -(hA.eigenvalues i)) := rfl

theorem antitone_sortedEigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    Antitone (sortedEigenvalues hA) := by
  have h := Tuple.monotone_sort (fun i => -(hA.eigenvalues i))
  intro i j hij
  have := h hij
  simpa [sortedEigenvalues, Function.comp] using this

end Sorted

section Main

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Von Neumann trace inequality, Hermitian case.**
If `A` and `B` are Hermitian matrices over an `RCLike` field, indexed by a finite linearly
ordered type, and `a`, `b` are the eigenvalue lists of `A` and `B` respectively, each
rearranged into decreasing order, then `Re (tr (A * B)) ≤ ∑ i, a i * b i`. -/
theorem vonNeumann_trace_ineq_hermitian [LinearOrder n] {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {a b : n → ℝ} {σ τ : Equiv.Perm n}
    (ha : a = hA.eigenvalues ∘ σ) (hb : b = hB.eigenvalues ∘ τ)
    (ha' : Antitone a) (hb' : Antitone b) :
    RCLike.re (trace (A * B)) ≤ ∑ i, a i * b i := by
  obtain ⟨W, hW1, hW2, htr⟩ := trace_mul_eq_sum_sq_norm hA hB
  rw [htr, RCLike.ofReal_re]
  set D : Matrix n n ℝ := (fun j k => ‖W j k‖ ^ 2 : Matrix n n ℝ) with hD
  have hDmem : D ∈ doublyStochastic ℝ n := sq_norm_mem_doublyStochastic W hW1 hW2
  have hD' : D.submatrix σ τ ∈ doublyStochastic ℝ n := by
    have := reindex_mem_doublyStochastic (e₁ := σ.symm) (e₂ := τ.symm) hDmem
    simpa [Matrix.reindex_apply] using this
  have hchange :
      ∑ j, ∑ k, hA.eigenvalues j * hB.eigenvalues k * ‖W j k‖ ^ 2
        = ∑ p, ∑ q, (D.submatrix σ τ) p q * (a p * b q) := by
    rw [← Equiv.sum_comp σ (fun j => ∑ k, hA.eigenvalues j * hB.eigenvalues k * ‖W j k‖ ^ 2)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Equiv.sum_comp τ
      (fun k => hA.eigenvalues (σ p) * hB.eigenvalues k * ‖W (σ p) k‖ ^ 2)]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [ha, hb, hD, Function.comp_apply, Matrix.submatrix_apply]
    ring
  rw [hchange]
  exact sum_mul_le_of_mem_doublyStochastic (monovary_of_antitone ha' hb') hD'

/-- **Von Neumann trace inequality, Hermitian case**, stated with the explicitly sorted
eigenvalue lists of matrices indexed by `Fin n`. -/
theorem vonNeumann_trace_ineq_hermitian_sorted {m : ℕ} {A B : Matrix (Fin m) (Fin m) 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (trace (A * B)) ≤ ∑ i, sortedEigenvalues hA i * sortedEigenvalues hB i :=
  vonNeumann_trace_ineq_hermitian hA hB (sortedEigenvalues_eq_comp hA)
    (sortedEigenvalues_eq_comp hB) (antitone_sortedEigenvalues hA) (antitone_sortedEigenvalues hB)

end Main

end Zeta23Core

