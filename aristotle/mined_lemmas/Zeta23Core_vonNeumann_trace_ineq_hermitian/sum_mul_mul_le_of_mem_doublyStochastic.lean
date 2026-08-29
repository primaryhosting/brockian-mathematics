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
