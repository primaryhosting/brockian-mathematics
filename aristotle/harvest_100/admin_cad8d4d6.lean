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

import Mathlib
/-!
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset Matrix

namespace Zeta23Redux.LinAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

omit [LinearOrder ι] in
/-- For a permutation matrix, the double sum `∑ i ∑ j (permMatrix σ) i j * (μ i * ν j)`
collapses to `∑ i, μ i * ν (σ i)`. -/
lemma sum_permMatrix_mul (σ : Equiv.Perm ι) (μ ν : ι → ℝ) :
    ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (μ i * ν j) = ∑ i, μ i * ν (σ i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Finset.sum_ite_eq', eq_comm]

omit [DecidableEq ι] in
/-- Rearrangement inequality for two antitone sequences: permuting one of them can only
decrease the sum of pointwise products. -/
lemma sum_mul_comp_perm_le (σ : Equiv.Perm ι) {μ ν : ι → ℝ}
    (hμ : Antitone μ) (hν : Antitone ν) :
    ∑ i, μ i * ν (σ i) ≤ ∑ i, μ i * ν i := by
  simpa [smul_eq_mul] using
    (hμ.monovary hν).sum_smul_comp_perm_le_sum_smul (σ := σ)

/-- **Rearrangement / Birkhoff step of the von Neumann trace inequality.**
If `S` is doubly stochastic and `μ`, `ν` are antitone weight sequences, then
`∑ᵢⱼ Sᵢⱼ · μᵢ · νⱼ ≤ ∑ᵢ μᵢ · νᵢ`. -/
theorem sum_doublyStochastic_mul_le {S : Matrix ι ι ℝ} (hS : S ∈ doublyStochastic ℝ ι)
    {μ ν : ι → ℝ} (hμ : Antitone μ) (hν : Antitone ν) :
    ∑ i, ∑ j, S i j * (μ i * ν j) ≤ ∑ i, μ i * ν i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hSij : ∀ i j, S i j = ∑ σ : Equiv.Perm ι, w σ * (σ.permMatrix ℝ) i j := by
    intro i j
    rw [← hwS]
    simp [Matrix.sum_apply, smul_eq_mul]
  have key : ∀ i, ∑ j, S i j * (μ i * ν j)
      = ∑ σ : Equiv.Perm ι, w σ * ∑ j, (σ.permMatrix ℝ) i j * (μ i * ν j) := by
    intro i
    simp_rw [hSij i, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hexp : ∑ i, ∑ j, S i j * (μ i * ν j)
      = ∑ σ : Equiv.Perm ι, w σ * ∑ i, μ i * ν (σ i) := by
    rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_permMatrix_mul]
  rw [hexp]
  calc ∑ σ : Equiv.Perm ι, w σ * ∑ i, μ i * ν (σ i)
      ≤ ∑ _σ : Equiv.Perm ι, w _σ * ∑ i, μ i * ν i := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left (sum_mul_comp_perm_le σ hμ hν) (hw0 σ)
    _ = ∑ i, μ i * ν i := by rw [← Finset.sum_mul, hw1, one_mul]

end Zeta23Redux.LinAlg

