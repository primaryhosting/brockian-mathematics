import Mathlib

/-!
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
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

namespace Zeta23Redux.LinAlg

open Finset Matrix

/-- Rearrangement inequality: for antitone weights, permuting one of them cannot increase the
pairing sum. -/
lemma sum_perm_mul_le {n : ℕ} (σ : Equiv.Perm (Fin n)) {mu nu : Fin n → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, mu i * nu (σ i) ≤ ∑ i, mu i * nu i := by
  simpa [smul_eq_mul] using (hmu.monovary hnu).sum_smul_comp_perm_le_sum_smul (σ := σ)

/--
**Rearrangement / Birkhoff step.**
If `S` is a doubly stochastic matrix and `mu`, `nu` are antitone weight sequences, then
`∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i`.
-/
theorem sum_doublyStochastic_mul_le {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin n)) {mu nu : Fin n → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hentry : ∀ i j, S i j = ∑ σ : Equiv.Perm (Fin n), w σ * (if σ i = j then 1 else 0) := by
    intro i j
    rw [← hwS]
    simp [Matrix.sum_apply, mul_ite]
  have hrow : ∀ i, ∑ j, S i j * (mu i * nu j)
      = ∑ σ : Equiv.Perm (Fin n), w σ * (mu i * nu (σ i)) := by
    intro i
    have : ∀ j, S i j * (mu i * nu j)
        = ∑ σ : Equiv.Perm (Fin n), w σ * (if σ i = j then 1 else 0) * (mu i * nu j) := by
      intro j; rw [hentry i j, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Finset.sum_ite_eq]
  have hrw : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, mu i * nu (σ i) := by
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm
  rw [hrw]
  calc ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, mu i * nu (σ i)
      ≤ ∑ _σ : Equiv.Perm (Fin n), w _σ * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left (sum_perm_mul_le σ hmu hnu) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

end Zeta23Redux.LinAlg

