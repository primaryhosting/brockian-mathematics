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
