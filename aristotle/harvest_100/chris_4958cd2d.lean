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
/-!
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Zeta23Redux.LinAlg

/-- **Rearrangement/Birkhoff step for the von Neumann trace inequality.**

If `S` is a doubly stochastic matrix and `μ`, `ν` are antitone (non-increasing) weight
sequences, then `∑ᵢⱼ Sᵢⱼ · μᵢ · νⱼ ≤ ∑ᵢ μᵢ · νᵢ`.

The proof combines Birkhoff's theorem (a doubly stochastic matrix is a convex combination
of permutation matrices) with the rearrangement inequality (`∑ᵢ μᵢ ν_{σ i} ≤ ∑ᵢ μᵢ νᵢ` for
monovarying families). -/
theorem sum_doublyStochastic_mul_le {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin n)) {μ ν : Fin n → ℝ}
    (hμ : Antitone μ) (hν : Antitone ν) :
    ∑ i, ∑ j, S i j * (μ i * ν j) ≤ ∑ i, μ i * ν i := by
  have hmono : Monovary μ ν := fun _ _ h => hμ (hν.reflect_lt h).le
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  subst hwS
  have key : ∀ σ : Equiv.Perm (Fin n), ∑ i, μ i * ν (σ i) ≤ ∑ i, μ i * ν i := by
    intro σ
    simpa using (hmono.monovaryOn (univ : Finset (Fin n))).sum_smul_comp_perm_le_sum_smul
      (σ := σ) (by simp)
  calc ∑ i, ∑ j, (∑ σ, w σ • Equiv.Perm.permMatrix ℝ σ) i j * (μ i * ν j)
      = ∑ σ, w σ * ∑ i, μ i * ν (σ i) := by
        simp [Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum, Equiv.Perm.permMatrix,
          PEquiv.toMatrix_apply, Finset.sum_comm (s := univ (α := Fin n))]
    _ ≤ ∑ σ, w σ * ∑ i, μ i * ν i :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (key σ) (hw0 σ)
    _ = ∑ i, μ i * ν i := by rw [← Finset.sum_mul, hw1, one_mul]

end Zeta23Redux.LinAlg

