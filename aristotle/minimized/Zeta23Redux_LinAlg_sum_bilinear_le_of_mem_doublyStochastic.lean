import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

open Matrix Finset

/-- Birkhoff + rearrangement: for antitone `mu`, `nu` and a doubly stochastic matrix `S`,
the bilinear form `∑ i j, S i j * (mu i * nu j)` is at most `∑ i, mu i * nu i`. -/

lemma sum_bilinear_le_of_mem_doublyStochastic {d : ℕ} {mu nu : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin d)) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have key : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) := by
    rw [← hwS]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, smul_eq_mul, Option.mem_some_iff, Finset.sum_mul]
    calc ∑ x : Fin d, ∑ y : Fin d, ∑ σ : Equiv.Perm (Fin d),
            (w σ * if σ x = y then 1 else 0) * (mu x * nu y)
        = ∑ x : Fin d, ∑ σ : Equiv.Perm (Fin d), ∑ y : Fin d,
            (w σ * if σ x = y then 1 else 0) * (mu x * nu y) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ σ : Equiv.Perm (Fin d), ∑ x : Fin d, ∑ y : Fin d,
            (w σ * if σ x = y then 1 else 0) * (mu x * nu y) := Finset.sum_comm
      _ = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [Finset.sum_ite_eq]
  rw [key]
  have hmono : Monovary mu nu := hmu.monovary hnu
  calc ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i)
      ≤ ∑ _σ : Equiv.Perm (Fin d), w _σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hmono.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
