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

/-- Two antitone functions on a linear order monovary. -/
theorem monovary_of_antitone {ι : Type*} [LinearOrder ι] {f g : ι → ℝ}
    (hf : Antitone f) (hg : Antitone g) : Monovary f g := by
  intro i j hij
  rcases le_total j i with h | h
  · exact hf h
  · exact absurd (hg h) (not_le.2 hij)

/-- A bilinear pairing against a doubly stochastic matrix, with monovarying weights, is bounded
by the "diagonal" pairing.  This is the rearrangement step in the von Neumann trace inequality. -/
theorem sum_mul_doublyStochastic_le {m : Type*} [Fintype m] [DecidableEq m]
    {S : Matrix m m ℝ} (hS : S ∈ doublyStochastic ℝ m) {a b : m → ℝ} (hab : Monovary a b) :
    ∑ j, ∑ k, a j * b k * S j k ≤ ∑ i, a i * b i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hentry : ∀ j k, S j k = ∑ σ : Equiv.Perm m, w σ * (σ.permMatrix ℝ) j k := by
    intro j k; rw [← hwS]; simp [Matrix.sum_apply]
  have hrow : ∀ j, ∑ k, a j * b k * S j k = ∑ σ : Equiv.Perm m, w σ * (a j * b (σ j)) := by
    intro j
    simp only [hentry, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 : ∑ k, a j * b k * (w σ * (σ.permMatrix ℝ) j k)
        = w σ * a j * ∑ k, b k * (σ.permMatrix ℝ) j k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1]
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, mul_assoc]
  calc ∑ j, ∑ k, a j * b k * S j k = ∑ σ : Equiv.Perm m, w σ * ∑ j, a j * b (σ j) := by
        simp only [hrow, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ ∑ σ : Equiv.Perm m, w σ * ∑ j, a j * b j :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hab.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of `Dₐ W D_b W*` written out in terms of the squared moduli of the entries of `W`. -/
theorem trace_diagonal_conj_eq (W : Matrix n n 𝕜) (a b : n → ℝ) :
    Matrix.trace (diagonal (RCLike.ofReal ∘ a) * W * diagonal (RCLike.ofReal ∘ b) * star W)
      = ((∑ j, ∑ k, a j * b k * ‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply]
  simp only [Function.comp_apply, RCLike.star_def]
  rw [show (a j : 𝕜) * W j k * (b k) * (starRingEnd 𝕜) (W j k)
      = (a j : 𝕜) * (b k) * (W j k * (starRingEnd 𝕜) (W j k)) by ring, RCLike.mul_conj]

/-- Conjugating by a unitary and cycling the trace: `tr ((U Dₐ U*)(V D_b V*)) = tr (Dₐ W D_b W*)`
for `W = U* V`. -/
theorem trace_conj_eq_trace_diagonal_conj {U V : Matrix n n 𝕜}
    (hUs : U * star U = 1) (hsU : star U * U = 1) (Da Db : Matrix n n 𝕜) :
    Matrix.trace ((U * Da * star U) * (V * Db * star V))
      = Matrix.trace (Da * (star U * V) * Db * star (star U * V)) := by
  have hform : (U * Da * star U) * (V * Db * star V)
      = U * (Da * (star U * V) * Db * star (star U * V)) * star U := by
    simp only [Matrix.star_mul, star_star, Matrix.mul_assoc, hUs, Matrix.mul_one]
  rw [hform, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hsU, Matrix.one_mul]

/-- The row sums of squared moduli of a unitary matrix are `1`. -/
theorem row_sum_normSq_of_unitary {W : Matrix n n 𝕜} (hW : W * star W = 1) (j : n) :
    ∑ k, ‖W j k‖ ^ 2 = 1 := by
  have hj : ∑ k, W j k * (starRingEnd 𝕜) (W j k) = 1 := by
    have := congrArg (fun M : Matrix n n 𝕜 => M j j) hW
    simpa only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply, RCLike.star_def]
      using this
  have h : ((∑ k, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← hj]
    push_cast
    exact Finset.sum_congr rfl fun k _ => (RCLike.mul_conj (W j k)).symm
  exact_mod_cast h

/-- The column sums of squared moduli of a unitary matrix are `1`. -/
theorem col_sum_normSq_of_unitary {W : Matrix n n 𝕜} (hW : star W * W = 1) (k : n) :
    ∑ j, ‖W j k‖ ^ 2 = 1 := by
  have hk : ∑ j, (starRingEnd 𝕜) (W j k) * W j k = 1 := by
    have := congrArg (fun M : Matrix n n 𝕜 => M k k) hW
    simpa only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply, RCLike.star_def]
      using this
  have h : ((∑ j, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← hk]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    exact (RCLike.mul_conj (W j k)).symm
  exact_mod_cast h

/-- The matrix of squared moduli of the entries of a unitary matrix is doubly stochastic. -/
theorem normSq_matrix_mem_doublyStochastic {W : Matrix n n 𝕜}
    (hW1 : W * star W = 1) (hW2 : star W * W = 1) :
    (Matrix.of fun j k => ‖W j k‖ ^ 2) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  exact ⟨fun i j => sq_nonneg _, fun i => row_sum_normSq_of_unitary hW1 i,
    fun j => col_sum_normSq_of_unitary hW2 j⟩

/-- **Von Neumann trace inequality, Hermitian case.**  For Hermitian matrices `A` and `B` over an
`RCLike` field, the real part of `trace (A * B)` is bounded by the sum of the products of the
eigenvalues of `A` and `B`, each sorted in decreasing order (`Matrix.IsHermitian.eigenvalues₀` is
antitone, see `Matrix.IsHermitian.eigenvalues₀_antitone`). -/
theorem vonNeumann_trace_ineq_hermitian {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (Matrix.trace (A * B)) ≤
      ∑ i : Fin (Fintype.card n), hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜)
  let V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜)
  let a : n → ℝ := hA.eigenvalues
  let b : n → ℝ := hB.eigenvalues
  let Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ a)
  let Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ b)
  have hUs : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hsU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hVs : V * star V = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hsV : star V * V = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  let W : Matrix n n 𝕜 := star U * V
  have hWstar : star W = star V * U := by
    show star (star U * V) = star V * U
    rw [Matrix.star_mul, star_star]
  have hW1 : W * star W = 1 := by
    show (star U * V) * star (star U * V) = 1
    rw [hWstar]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V (star V) U, hVs, Matrix.one_mul, hsU]
  have hW2 : star W * W = 1 := by
    show star (star U * V) * (star U * V) = 1
    rw [hWstar]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U (star U) V, hUs, Matrix.one_mul, hsV]
  -- Step 1: rewrite the trace as `tr (Dₐ W D_b W*)`
  have htr : Matrix.trace (A * B) = Matrix.trace (Da * W * Db * star W) := by
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    exact trace_conj_eq_trace_diagonal_conj hUs hsU Da Db
  -- Step 2: the weight matrix of squared moduli is doubly stochastic
  let S : Matrix n n ℝ := Matrix.of fun j k => ‖W j k‖ ^ 2
  have hSentry : ∀ j k, S j k = ‖W j k‖ ^ 2 := fun _ _ => rfl
  have hSds : S ∈ doublyStochastic ℝ n := normSq_matrix_mem_doublyStochastic hW1 hW2
  have hre : RCLike.re (Matrix.trace (A * B)) = ∑ j, ∑ k, a j * b k * S j k := by
    rw [htr, trace_diagonal_conj_eq W a b, RCLike.ofReal_re]
    simp only [hSentry]
  -- Step 3: reindex to `Fin (Fintype.card n)` and apply the rearrangement bound
  let S' : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ := S.reindex e.symm e.symm
  have hS'entry : ∀ p q, S' p q = S (e p) (e q) := fun p q => rfl
  have hS'ds : S' ∈ doublyStochastic ℝ (Fin (Fintype.card n)) :=
    reindex_mem_doublyStochastic hSds
  have hae : ∀ p, a (e p) = hA.eigenvalues₀ p := by
    intro p
    show hA.eigenvalues (e p) = hA.eigenvalues₀ p
    simp [Matrix.IsHermitian.eigenvalues, e]
  have hbe : ∀ p, b (e p) = hB.eigenvalues₀ p := by
    intro p
    show hB.eigenvalues (e p) = hB.eigenvalues₀ p
    simp [Matrix.IsHermitian.eigenvalues, e]
  have hsum : ∑ j, ∑ k, a j * b k * S j k
      = ∑ p, ∑ q, hA.eigenvalues₀ p * hB.eigenvalues₀ q * S' p q := by
    rw [← Equiv.sum_comp e (fun j => ∑ k, a j * b k * S j k)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Equiv.sum_comp e (fun k => a (e p) * b k * S (e p) k)]
    exact Finset.sum_congr rfl fun q _ => by rw [hae, hbe, hS'entry]
  rw [hre, hsum]
  exact sum_mul_doublyStochastic_le hS'ds
    (monovary_of_antitone hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone)

end Zeta23Core

