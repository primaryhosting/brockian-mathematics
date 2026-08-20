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

/-- Two antitone sequences on a linear order monovary. -/
lemma monovary_of_antitone {n : Type*} [LinearOrder n] {μ ν : n → ℝ}
    (hμ : Antitone μ) (hν : Antitone ν) : Monovary μ ν := by
  intro i j hij
  have hji : j < i := by
    by_contra h
    exact absurd (hν (not_lt.1 h)) (not_le.2 hij)
  exact hμ hji.le

/-- For a permutation matrix, the weighted sum reduces to a permuted sum, which is bounded
by the aligned sum by the rearrangement inequality. -/
lemma sum_permMatrix_mul_le {n : Type*} [Fintype n] [LinearOrder n] (σ : Equiv.Perm n)
    {μ ν : n → ℝ} (hμ : Antitone μ) (hν : Antitone ν) :
    ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (μ i * ν j) ≤ ∑ i, μ i * ν i := by
  have hrow : ∀ i : n, ∑ j, (σ.permMatrix ℝ) i j * (μ i * ν j) = μ i * ν (σ i) := by
    intro i
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  calc ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (μ i * ν j) = ∑ i, μ i * ν (σ i) := by
        exact Finset.sum_congr rfl fun i _ => hrow i
    _ ≤ ∑ i, μ i * ν i := (monovary_of_antitone hμ hν).sum_smul_comp_perm_le_sum_smul

/-- **Rearrangement / Birkhoff step.** For a doubly stochastic matrix `S` and antitone weight
sequences `μ`, `ν`, we have `∑ᵢ ∑ⱼ Sᵢⱼ · μᵢ · νⱼ ≤ ∑ᵢ μᵢ · νᵢ`. -/
theorem sum_doublyStochastic_mul_le {n : Type*} [Fintype n] [LinearOrder n]
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) {μ ν : n → ℝ}
    (hμ : Antitone μ) (hν : Antitone ν) :
    ∑ i, ∑ j, S i j * (μ i * ν j) ≤ ∑ i, μ i * ν i := by
  have hlin : IsLinearMap ℝ (fun M : Matrix n n ℝ => ∑ i, ∑ j, M i j * (μ i * ν j)) := by
    constructor
    · intro M N
      simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    · intro c M
      simp [Matrix.smul_apply, Finset.mul_sum, mul_assoc]
  have hsub : {x : Matrix n n ℝ | ∃ σ : Equiv.Perm n, σ.permMatrix ℝ = x} ⊆
      {M : Matrix n n ℝ | ∑ i, ∑ j, M i j * (μ i * ν j) ≤ ∑ i, μ i * ν i} := by
    rintro x ⟨σ, rfl⟩
    exact sum_permMatrix_mul_le σ hμ hν
  have hconv := convex_halfSpace_le hlin (∑ i, μ i * ν i)
  have hmem : S ∈ (convexHull ℝ) {x : Matrix n n ℝ | ∃ σ : Equiv.Perm n, σ.permMatrix ℝ = x} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]
    exact hS
  exact convexHull_min hsub hconv hmem

end Zeta23Redux.LinAlg

