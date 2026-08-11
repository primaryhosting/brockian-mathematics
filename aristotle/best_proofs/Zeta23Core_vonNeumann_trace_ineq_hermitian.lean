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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix Finset

/-! ### A rearrangement bound for doubly stochastic matrices -/

/-- If `a` and `b` monovary, then the bilinear form `∑ j k, D j k * (a j * b k)` attached to a
doubly stochastic matrix `D` is at most `∑ i, a i * b i`.  This is the combinatorial heart of the
von Neumann trace inequality: it follows from Birkhoff's theorem together with the rearrangement
inequality. -/
lemma sum_bilin_le_of_mem_doublyStochastic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℝ} (hab : Monovary a b)
    {D : Matrix ι ι ℝ} (hD : D ∈ doublyStochastic ℝ ι) :
    ∑ j, ∑ k, D j k * (a j * b k) ≤ ∑ i, a i * b i := by
  obtain ⟨w, hw0, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  have hentry : ∀ j k, D j k = ∑ σ : Equiv.Perm ι, w σ * (if σ j = k then 1 else 0) := by
    intro j k
    rw [← hwD]
    simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  have hrow : ∀ j, ∑ k, D j k * (a j * b k) = ∑ σ : Equiv.Perm ι, w σ * (a j * b (σ j)) := by
    intro j
    simp_rw [hentry j, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Finset.sum_ite_eq]
  have key : ∑ j, ∑ k, D j k * (a j * b k)
      = ∑ σ : Equiv.Perm ι, w σ * ∑ j, a j * b (σ j) := by
    simp_rw [hrow]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [key]
  calc ∑ σ : Equiv.Perm ι, w σ * ∑ j, a j * b (σ j)
      ≤ ∑ _σ : Equiv.Perm ι, w _σ * ∑ j, a j * b j :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hab.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

/-! ### Auxiliary matrix computations -/

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared moduli of the entries of a unitary matrix form a doubly stochastic matrix. -/
lemma normSq_mem_doublyStochastic {M : Matrix n n 𝕜} (h1 : M * Mᴴ = 1) (h2 : Mᴴ * M = 1) :
    (Matrix.of fun j k => ‖M j k‖ ^ 2 : Matrix n n ℝ) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by simp only [Matrix.of_apply]; positivity, fun j => ?_, fun k => ?_⟩
  · have h := congrFun (congrFun h1 j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    have hc : ((∑ k, ‖M j k‖ ^ 2 : ℝ) : 𝕜) = ((1 : ℝ) : 𝕜) := by
      push_cast
      rw [← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.mul_conj]
    simpa using RCLike.ofReal_injective hc
  · have h := congrFun (congrFun h2 k) k
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    have hc : ((∑ j, ‖M j k‖ ^ 2 : ℝ) : 𝕜) = ((1 : ℝ) : 𝕜) := by
      push_cast
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, RCLike.star_def, mul_comm, RCLike.mul_conj]
    simpa using RCLike.ofReal_injective hc

/-- Expansion of `tr (Dₐ M D_b Mᴴ)` for real diagonal matrices `Dₐ`, `D_b`. -/
lemma trace_diag_mul_diag_conj (a b : n → ℝ) (M : Matrix n n 𝕜) :
    Matrix.trace (Matrix.diagonal (fun i => (a i : 𝕜)) * M *
        Matrix.diagonal (fun i => (b i : 𝕜)) * Mᴴ)
      = ∑ j, ∑ k, ((a j * b k * ‖M j k‖ ^ 2 : ℝ) : 𝕜) := by
  have hprod : Matrix.diagonal (fun i => (a i : 𝕜)) * M * Matrix.diagonal (fun i => (b i : 𝕜))
      = Matrix.of (fun j k => (a j : 𝕜) * M j k * (b k : 𝕜)) := by
    ext j k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  rw [hprod, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, Matrix.of_apply]
  have h2 : M j k * star (M j k) = ((‖M j k‖ : 𝕜)) ^ 2 := by
    rw [RCLike.star_def, RCLike.mul_conj]
  push_cast
  linear_combination ((a j : 𝕜) * (b k : 𝕜)) * h2

omit [DecidableEq n] in
/-- Moving the conjugations onto a single unitary factor inside a trace. -/
lemma trace_conj_mul_conj (U V Da Db : Matrix n n 𝕜) :
    Matrix.trace ((U * Da * star U) * (V * Db * star V))
      = Matrix.trace (Da * (star U * V) * Db * star (star U * V)) := by
  have h1 : (U * Da * star U) * (V * Db * star V)
      = U * (Da * (star U * V) * Db * star V) := by
    simp [mul_assoc]
  rw [h1, Matrix.trace_mul_comm, Matrix.star_mul, star_star]
  congr 1
  simp [mul_assoc]

/-- The eigenvalue functions of two Hermitian matrices monovary, since both are obtained from
antitone functions by the same reindexing. -/
lemma monovary_eigenvalues {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Monovary hA.eigenvalues hB.eigenvalues := by
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  intro i j hij
  have hAi : hA.eigenvalues i = hA.eigenvalues₀ (e.symm i) := rfl
  have hAj : hA.eigenvalues j = hA.eigenvalues₀ (e.symm j) := rfl
  have hBi : hB.eigenvalues i = hB.eigenvalues₀ (e.symm i) := rfl
  have hBj : hB.eigenvalues j = hB.eigenvalues₀ (e.symm j) := rfl
  rw [hAi, hAj]
  rcases le_or_gt (e.symm j) (e.symm i) with h | h
  · exact hA.eigenvalues₀_antitone h
  · rw [hBi, hBj] at hij
    exact absurd (hB.eigenvalues₀_antitone h.le) (not_le.2 hij)

/-! ### The von Neumann trace inequality -/

/-- **Von Neumann trace inequality**, Hermitian case.  For Hermitian matrices `A`, `B` over an
`RCLike` field, the real part of `tr (A * B)` is at most the sum of the products of the
eigenvalues of `A` and of `B`, each listed in decreasing order (`Matrix.IsHermitian.eigenvalues₀`
is antitone by `Matrix.IsHermitian.eigenvalues₀_antitone`). -/
theorem vonNeumann_trace_ineq_hermitian {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (Matrix.trace (A * B)) ≤
      ∑ i : Fin (Fintype.card n), hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  classical
  -- the unitary `M` relating the two eigenbases
  set mu : Matrix.unitaryGroup n 𝕜 := star hA.eigenvectorUnitary * hB.eigenvectorUnitary with hmu
  set M : Matrix n n 𝕜 := (mu : Matrix n n 𝕜) with hM
  have hMu : M ∈ unitary (Matrix n n 𝕜) := mu.2
  have hM1 : M * Mᴴ = 1 := by
    have := hMu.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have hM2 : Mᴴ * M = 1 := by
    have := hMu.1
    rwa [Matrix.star_eq_conjTranspose] at this
  -- spectral decompositions
  set Da : Matrix n n 𝕜 := Matrix.diagonal (fun i => (hA.eigenvalues i : 𝕜)) with hDa
  set Db : Matrix n n 𝕜 := Matrix.diagonal (fun i => (hB.eigenvalues i : 𝕜)) with hDb
  have hAeq : A = (hA.eigenvectorUnitary : Matrix n n 𝕜) * Da *
      star (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hBeq : B = (hB.eigenvectorUnitary : Matrix n n 𝕜) * Db *
      star (hB.eigenvectorUnitary : Matrix n n 𝕜) := by
    conv_lhs => rw [hB.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hMeq : M = star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      (hB.eigenvectorUnitary : Matrix n n 𝕜) := rfl
  -- expand the trace
  have htrace : Matrix.trace (A * B) = ∑ j, ∑ k,
      ((hA.eigenvalues j * hB.eigenvalues k * ‖M j k‖ ^ 2 : ℝ) : 𝕜) := by
    conv_lhs => rw [hAeq, hBeq]
    rw [trace_conj_mul_conj, ← hMeq, Matrix.star_eq_conjTranspose, hDa, hDb,
      trace_diag_mul_diag_conj]
  have hre : RCLike.re (Matrix.trace (A * B))
      = ∑ j, ∑ k, (Matrix.of fun j k => ‖M j k‖ ^ 2 : Matrix n n ℝ) j k *
        (hA.eigenvalues j * hB.eigenvalues k) := by
    rw [htrace]
    simp only [map_sum, RCLike.ofReal_re, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hre]
  refine le_trans (sum_bilin_le_of_mem_doublyStochastic (monovary_eigenvalues hA hB)
    (normSq_mem_doublyStochastic hM1 hM2)) ?_
  -- reindex the right-hand side
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  have : ∑ i : n, hA.eigenvalues i * hB.eigenvalues i
      = ∑ i : Fin (Fintype.card n), hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
    rw [← Equiv.sum_comp e (fun i => hA.eigenvalues i * hB.eigenvalues i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : hA.eigenvalues (e i) = hA.eigenvalues₀ (e.symm (e i)) := rfl
    have h2 : hB.eigenvalues (e i) = hB.eigenvalues₀ (e.symm (e i)) := rfl
    rw [h1, h2, Equiv.symm_apply_apply]
  exact le_of_eq this

end Zeta23Core

#print axioms Zeta23Core.vonNeumann_trace_ineq_hermitian

