import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared moduli along a row of a unitary matrix sum to `1`. -/

lemma sum_bilin_le_of_doublyStochastic (mu nu : n → ℝ) (hmn : Monovary mu nu)
    (S : Matrix n n ℝ) (hS : S ∈ doublyStochastic ℝ n) :
    ∑ i, ∑ j, mu i * nu j * S i j ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hSij : ∀ i j, S i j = ∑ σ : Equiv.Perm n, w σ * (σ.permMatrix ℝ) i j := by
    intro i j
    rw [← hwS]
    simp [Matrix.sum_apply]
  have hinner : ∀ (σ : Equiv.Perm n) (i : n),
      ∑ j, mu i * nu j * (w σ * (σ.permMatrix ℝ) i j) = w σ * (mu i * nu (σ i)) := by
    intro σ i
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, mul_comm,
      mul_left_comm]
  have key : ∑ i, ∑ j, mu i * nu j * S i j
      = ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i) := by
    calc ∑ i, ∑ j, mu i * nu j * S i j
        = ∑ i, ∑ j, ∑ σ : Equiv.Perm n, mu i * nu j * (w σ * (σ.permMatrix ℝ) i j) := by
          simp only [hSij, Finset.mul_sum]
      _ = ∑ i, ∑ σ : Equiv.Perm n, ∑ j, mu i * nu j * (w σ * (σ.permMatrix ℝ) i j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ σ : Equiv.Perm n, ∑ i, ∑ j, mu i * nu j * (w σ * (σ.permMatrix ℝ) i j) :=
          Finset.sum_comm
      _ = ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => hinner σ i
  rw [key]
  calc ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i)
      ≤ ∑ _σ : Equiv.Perm n, w _σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hmn.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Von Neumann's trace inequality, in the form where the two Hermitian matrices are given
explicitly as unitary conjugates of real diagonal matrices, and `mu`, `nu` are arbitrary
rearrangements of the diagonals that monovary. -/
