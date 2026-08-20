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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Redux.LinAlg

open Finset Matrix

/-- Antitone sequences monovary. -/
lemma monovary_of_antitone {n : ℕ} {mu nu : Fin n → ℝ} (hmu : Antitone mu) (hnu : Antitone nu) :
    Monovary mu nu := by
  intro i j hij
  exact hmu (le_of_lt (lt_of_not_ge fun h => absurd (hnu h) (not_le_of_gt hij)))

/-- Contracting a permutation matrix against `μ ⊗ ν` gives the permuted pairing. -/
lemma sum_permMatrix_mul {n : ℕ} (sigma : Equiv.Perm (Fin n)) (mu nu : Fin n → ℝ) :
    ∑ i, ∑ j, (sigma.permMatrix ℝ) i j * mu i * nu j = ∑ i, mu i * nu (sigma i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Finset.sum_ite_eq]

/-- For a doubly stochastic matrix `S` and antitone weight sequences `μ`, `ν`,
the pairing `∑ᵢⱼ Sᵢⱼ μᵢ νⱼ` is at most the diagonal pairing `∑ᵢ μᵢ νᵢ`.
This is the rearrangement/Birkhoff step feeding the von Neumann trace inequality. -/
theorem sum_doublyStochastic_mul_le {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin n)) {mu nu : Fin n → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, S i j * mu i * nu j ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hmono : Monovary mu nu := monovary_of_antitone hmu hnu
  have key : ∑ i, ∑ j, S i j * mu i * nu j
      = ∑ sigma : Equiv.Perm (Fin n), w sigma * ∑ i, mu i * nu (sigma i) := by
    have hSij : ∀ i j, S i j = ∑ sigma : Equiv.Perm (Fin n), w sigma * (sigma.permMatrix ℝ) i j := by
      intro i j
      rw [← hwS]
      simp [Matrix.sum_apply, Matrix.smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp_rw [hSij, Finset.sum_mul, ← sum_permMatrix_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm (γ := Equiv.Perm (Fin n))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (γ := Equiv.Perm (Fin n))]
  rw [key]
  calc ∑ sigma : Equiv.Perm (Fin n), w sigma * ∑ i, mu i * nu (sigma i)
      ≤ ∑ _s : Equiv.Perm (Fin n), w _s * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun sigma _ => ?_
        have := hmono.sum_smul_comp_perm_le_sum_smul (σ := sigma)
        simp only [smul_eq_mul] at this
        exact mul_le_mul_of_nonneg_left this (hw0 sigma)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

end Zeta23Redux.LinAlg

