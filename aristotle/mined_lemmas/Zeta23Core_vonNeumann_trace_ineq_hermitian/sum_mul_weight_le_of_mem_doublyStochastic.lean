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
