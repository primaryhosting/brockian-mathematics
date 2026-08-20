/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Zeta23Redux.LinAlg

open Matrix Finset

section Core

variable {d : ℕ}

/-- Two antitone real sequences monovary. -/

lemma sum_mul_doublyStochastic_le {mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S ∈ doublyStochastic ℝ (Fin d)) :
    ∑ i, ∑ j, mu i * nu j * S i j ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hentry : ∀ i j, S i j = ∑ σ : Equiv.Perm (Fin d), w σ * (σ.permMatrix ℝ i j) := by
    intro i j
    rw [← hwS]
    simp [Matrix.sum_apply, smul_eq_mul]
  have hperm : ∀ σ : Equiv.Perm (Fin d),
      ∑ i, ∑ j, mu i * nu j * (σ.permMatrix ℝ i j) = ∑ i, mu i * nu (σ i) := by
    intro σ
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : ∀ j : Fin d, mu i * nu j * (σ.permMatrix ℝ i j)
        = if j = σ i then mu i * nu j else 0 := by
      intro j
      by_cases hj : j = σ i
      · subst hj; simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
          Ne.symm hj, hj]
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq' Finset.univ (σ i)]
    simp
  calc ∑ i, ∑ j, mu i * nu j * S i j
      = ∑ i, ∑ j, ∑ σ : Equiv.Perm (Fin d), w σ * (mu i * nu j * (σ.permMatrix ℝ i j)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hentry i j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
    _ = ∑ i, ∑ σ : Equiv.Perm (Fin d), ∑ j, w σ * (mu i * nu j * (σ.permMatrix ℝ i j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin d), ∑ i, ∑ j, w σ * (mu i * nu j * (σ.permMatrix ℝ i j)) :=
        Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, ∑ j, mu i * nu j * (σ.permMatrix ℝ i j) := by
        simp [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) :=
        Finset.sum_congr rfl fun σ _ => by rw [hperm σ]
    _ ≤ ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left
          ((monovary_of_antitone hmu hnu).sum_mul_comp_perm_le_sum_mul) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

end Core

section Spectral

variable {d : ℕ}

/-- Spectral theorem for Hermitian matrices, with the eigenvalues listed in an arbitrary
(permuted) order. -/
