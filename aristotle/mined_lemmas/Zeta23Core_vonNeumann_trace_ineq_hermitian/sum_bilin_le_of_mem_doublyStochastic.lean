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
