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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared moduli of the entries of `W`. If `W` is unitary this is a doubly
stochastic matrix. -/
noncomputable def weightMatrix (W : Matrix n n 𝕜) : Matrix n n ℝ :=
  Matrix.of fun j k => ‖W j k‖ ^ 2

omit [Fintype n] [DecidableEq n] in
@[simp] lemma weightMatrix_apply (W : Matrix n n 𝕜) (j k : n) :
    weightMatrix W j k = ‖W j k‖ ^ 2 := rfl

/-- The squared-modulus matrix of a unitary matrix is doubly stochastic. -/
lemma weightMatrix_mem_doublyStochastic {W : Matrix n n 𝕜}
    (h₁ : W * star W = 1) (h₂ : star W * W = 1) :
    weightMatrix W ∈ doublyStochastic ℝ n := by
  have hz : ∀ z : 𝕜, z * star z = ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    intro z; rw [RCLike.star_def, RCLike.mul_conj]; push_cast; ring
  have hz' : ∀ z : 𝕜, star z * z = ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    intro z; rw [RCLike.star_def, RCLike.conj_mul]; push_cast; ring
  refine mem_doublyStochastic_iff_sum.2 ⟨fun j k => by rw [weightMatrix_apply]; positivity, fun j => ?_, fun k => ?_⟩
  · have h := congrFun (congrFun h₁ j) j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, hz, Matrix.one_apply_eq, ← RCLike.ofReal_sum] at h
    simpa using (by exact_mod_cast h : ∑ k, ‖W j k‖ ^ 2 = (1 : ℝ))
  · have h := congrFun (congrFun h₂ k) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, hz', Matrix.one_apply_eq, ← RCLike.ofReal_sum] at h
    simpa using (by exact_mod_cast h : ∑ j, ‖W j k‖ ^ 2 = (1 : ℝ))

/-- Maximizing the bilinear form `S ↦ ∑ⱼₖ aⱼ b_k Sⱼₖ` over doubly stochastic matrices:
by Birkhoff's theorem `S` is a convex combination of permutation matrices, and for each
permutation the rearrangement inequality applies. -/
lemma sum_mul_mul_le_of_mem_doublyStochastic {a b : n → ℝ} (hab : Monovary a b)
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) :
    ∑ j, ∑ k, a j * b k * S j k ≤ ∑ i, a i * b i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have happ : ∀ j k, S j k = ∑ σ : Equiv.Perm n, w σ * (if σ j = k then 1 else 0) := by
    intro j k
    rw [← hwS]
    simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have key : ∑ j, ∑ k, a j * b k * S j k = ∑ σ : Equiv.Perm n, w σ * ∑ j, a j * b (σ j) := by
    have step : ∀ j : n, ∑ k, a j * b k * S j k
        = ∑ σ : Equiv.Perm n, w σ * (a j * b (σ j)) := by
      intro j
      simp only [happ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_eq_single (σ j)]
      · simp; ring
      · intro k _ hk; simp [Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [step]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => by rw [Finset.mul_sum]
  rw [key]
  calc ∑ σ : Equiv.Perm n, w σ * ∑ j, a j * b (σ j)
      ≤ ∑ _σ : Equiv.Perm n, w _σ * ∑ i, a i * b i :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hab.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The real part of the trace of `diag a * W * diag b * Wᴴ`, in terms of the weight matrix
of `W`. -/
lemma re_trace_diag_mul {a b : n → ℝ} (W : Matrix n n 𝕜) :
    RCLike.re (Matrix.trace (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * W *
        diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star W))
      = ∑ j, ∑ k, a j * b k * weightMatrix W j k := by
  have hz : ∀ z : 𝕜, z * star z = ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    intro z; rw [RCLike.star_def, RCLike.mul_conj]; push_cast; ring
  have hd : ∀ j : n, (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * W *
      diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star W) j j
      = ((∑ k, a j * b k * weightMatrix W j k : ℝ) : 𝕜) := by
    intro j
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply]
    simp only [Function.comp_apply, weightMatrix_apply]
    rw [show (a j : 𝕜) * W j k * (b k : 𝕜) * star (W j k)
        = ((a j : 𝕜) * (b k : 𝕜)) * (W j k * star (W j k)) by ring, hz]
  simp only [Matrix.trace, Matrix.diag_apply, hd, ← RCLike.ofReal_sum, RCLike.ofReal_re]

/-- Von Neumann's trace inequality in diagonalized form: if `U` and `V` are unitary and the
real vectors `a` and `b` monovary, then `Re tr (U diag(a) Uᴴ V diag(b) Vᴴ) ≤ ∑ᵢ aᵢ bᵢ`. -/
lemma re_trace_conj_le {a b : n → ℝ} (hab : Monovary a b) {U V : Matrix n n 𝕜}
    (hU : U * star U = 1) (hU' : star U * U = 1)
    (hV : V * star V = 1) (hV' : star V * V = 1) :
    RCLike.re (Matrix.trace (U * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * star U *
        (V * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star V))) ≤ ∑ i, a i * b i := by
  set W : Matrix n n 𝕜 := star U * V with hW
  have hstarW : star W = star V * U := by rw [hW, Matrix.star_mul, star_star]
  have hWW : W * star W = 1 := by
    rw [hW, hstarW]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by simp only [mul_assoc]
      _ = 1 := by rw [hV, mul_one, hU']
  have hWW' : star W * W = 1 := by
    rw [hW, hstarW]
    calc star V * U * (star U * V) = star V * (U * star U) * V := by simp only [mul_assoc]
      _ = 1 := by rw [hU, mul_one, hV']
  have htr : Matrix.trace (U * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * star U *
      (V * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star V))
      = Matrix.trace (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * W *
        diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star W) := by
    have e1 : U * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * star U *
        (V * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star V)
        = U * (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * star U * V *
          diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star V) := by
      simp only [mul_assoc]
    rw [e1, Matrix.trace_mul_comm, hstarW, hW]
    congr 1
    simp only [mul_assoc]
  rw [htr, re_trace_diag_mul]
  exact sum_mul_mul_le_of_mem_doublyStochastic hab
    (weightMatrix_mem_doublyStochastic hWW hWW')

lemma monovary_eigenvalues {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Monovary hA.eigenvalues hB.eigenvalues := by
  intro i j hij
  unfold Matrix.IsHermitian.eigenvalues at *
  set e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
  rcases le_total (e i) (e j) with h | h
  · exact absurd (hB.eigenvalues₀_antitone h) (not_le.2 hij)
  · exact hA.eigenvalues₀_antitone h

lemma sum_eigenvalues₀_mul {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i
      = ∑ i : n, hA.eigenvalues i * hB.eigenvalues i := by
  unfold Matrix.IsHermitian.eigenvalues
  rw [← Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
    (fun j => hA.eigenvalues₀ j * hB.eigenvalues₀ j)]

/-- **Von Neumann trace inequality, Hermitian case.**
For Hermitian matrices `A`, `B` over an `RCLike` field, the real part of `tr (A * B)` is at most
the sum of the products of their eigenvalues, each sorted in decreasing order.  Decreasing
sortedness is expressed by using `Matrix.IsHermitian.eigenvalues₀`, which is antitone (see
`Matrix.IsHermitian.eigenvalues₀_antitone`). -/
theorem vonNeumann_trace_ineq_hermitian {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (Matrix.trace (A * B)) ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  have hAeq : A = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hA.eigenvalues) *
      star (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
    simpa using hA.spectral_theorem
  have hBeq : B = (hB.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hB.eigenvalues) *
      star (hB.eigenvectorUnitary : Matrix n n 𝕜) := by
    simpa using hB.spectral_theorem
  rw [sum_eigenvalues₀_mul hA hB]
  conv_lhs => rw [hAeq, hBeq]
  exact re_trace_conj_le (monovary_eigenvalues hA hB)
    (by exact_mod_cast Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2)
    (by exact_mod_cast Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2)
    (by exact_mod_cast Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2)
    (by exact_mod_cast Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2)

end Zeta23Core

