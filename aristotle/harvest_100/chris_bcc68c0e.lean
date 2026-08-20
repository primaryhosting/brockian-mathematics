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

open Finset Matrix

namespace Zeta23Redux.LinAlg

/-- **Rearrangement / Birkhoff step for the von Neumann trace inequality.**

If `S` is a doubly stochastic matrix and `mu`, `nu` are antitone weight sequences, then
`∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i`.

The proof writes `S` as a convex combination of permutation matrices (Birkhoff's theorem) and
applies the rearrangement inequality to each permutation. -/
theorem sum_doublyStochastic_mul_le {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin n)) {mu nu : Fin n → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  -- Antitone sequences monovary.
  have hmon : Monovary mu nu := by
    intro i j h
    rcases le_total i j with hij | hij
    · exact absurd (hnu hij) (not_le.2 h)
    · exact hmu hij
  -- Birkhoff: `S` is a convex combination of permutation matrices.
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hentry : ∀ i j, S i j = ∑ σ : Equiv.Perm (Fin n), w σ * (σ.permMatrix ℝ i j) := by
    intro i j
    rw [← hwS]
    simp [Matrix.sum_apply]
  have key : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, mu i * nu (σ i) := by
    have hrow : ∀ i, ∑ j, S i j * (mu i * nu j)
        = ∑ σ : Equiv.Perm (Fin n), w σ * (mu i * nu (σ i)) := by
      intro i
      simp only [hentry, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      have hfac : ∑ j, w σ * (σ.permMatrix ℝ i j) * (mu i * nu j)
          = w σ * mu i * ∑ j, (σ.permMatrix ℝ i j) * nu j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hfac]
      simp [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, mul_assoc]
    simp only [hrow]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => by rw [Finset.mul_sum]
  rw [key]
  calc ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, mu i * nu (σ i)
      ≤ ∑ _σ : Equiv.Perm (Fin n), w _σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hmon.sum_smul_comp_perm_le_sum_smul (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

end Zeta23Redux.LinAlg

