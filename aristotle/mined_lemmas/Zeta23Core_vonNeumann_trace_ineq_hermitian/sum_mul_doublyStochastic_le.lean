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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a unitary matrix `W`, the matrix of squared norms of the entries of `W` is doubly
stochastic: its rows sum to `1` because `W * Wᴴ = 1`, and its columns sum to `1` because
`Wᴴ * W = 1`. -/

lemma sum_mul_doublyStochastic_le {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {a b : ι → ℝ} (ha : Antitone a) (hb : Antitone b) {M : Matrix ι ι ℝ}
    (hM : M ∈ doublyStochastic ℝ ι) :
    ∑ j, ∑ k, a j * b k * M j k ≤ ∑ i, a i * b i := by
  obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hmono : Monovary a b := ha.monovary hb
  have expand : ∀ j k, M j k = ∑ σ : Equiv.Perm ι, w σ * (σ.permMatrix ℝ) j k := by
    intro j k
    rw [← hwM]
    simp [Matrix.sum_apply]
  have key : ∀ σ : Equiv.Perm ι, ∑ j, ∑ k, a j * b k * (σ.permMatrix ℝ) j k
      = ∑ j, a j * b (σ j) := by
    intro σ
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have step1 : ∀ j : ι, ∑ k, a j * b k * M j k
      = ∑ σ : Equiv.Perm ι, ∑ k, w σ * (a j * b k * (σ.permMatrix ℝ) j k) := by
    intro j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [expand j k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  calc ∑ j, ∑ k, a j * b k * M j k
      = ∑ σ : Equiv.Perm ι, w σ * ∑ j, ∑ k, a j * b k * (σ.permMatrix ℝ) j k := by
        simp_rw [step1]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm ι, w σ * ∑ j, a j * b (σ j) :=
        Finset.sum_congr rfl fun σ _ => by rw [key σ]
    _ ≤ ∑ σ : Equiv.Perm ι, w σ * ∑ j, a j * b j :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hmono.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The real part of the trace of a product of two unitarily diagonalized Hermitian matrices,
written as `∑ j k, a j * b k * |W j k|²` for the unitary `W = Uᴴ V`. -/
