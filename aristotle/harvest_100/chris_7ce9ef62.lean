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

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- Two antitone functions monovary. -/
lemma monovary_of_antitone {n : Type*} [LinearOrder n] {f g : n → ℝ}
    (hf : Antitone f) (hg : Antitone g) : Monovary f g := by
  intro i j h
  have hji : j ≤ i := by
    by_contra hc
    exact absurd (hg (le_of_lt (lt_of_not_ge hc))) (not_le.2 h)
  exact hf hji

/-- For a permutation matrix, the bilinear form `∑ i j, P i j * (μ i * ν j)` is
`∑ i, μ i * ν (σ i)`. -/
lemma sum_permMatrix_mul {n : Type*} [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm n) (mu nu : n → ℝ) :
    ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (mu i * nu j) = ∑ i, mu i * nu (σ i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (σ i)]
  · simp [PEquiv.toMatrix_apply]
  · intro j _ hj
    simp [PEquiv.toMatrix_apply, hj.symm]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Rearrangement / Birkhoff step.** If `S` is doubly stochastic and `μ`, `ν` are antitone
weight sequences, then `∑ i j, S i j * (μ i * ν j) ≤ ∑ i, μ i * ν i`. -/
theorem sum_doublyStochastic_mul_le {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n)
    {mu nu : n → ℝ} (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  classical
  obtain ⟨w, hw0, hw1, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hmono : Monovary mu nu := monovary_of_antitone hmu hnu
  have step : ∀ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i)
      = ∑ i, ∑ j, w σ * ((σ.permMatrix ℝ) i j * (mu i * nu j)) := by
    intro σ
    rw [← sum_permMatrix_mul σ mu nu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  have hexp : ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i)
      = ∑ i, ∑ j, S i j * (mu i * nu j) := by
    calc ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i)
        = ∑ σ : Equiv.Perm n, ∑ i, ∑ j, w σ * ((σ.permMatrix ℝ) i j * (mu i * nu j)) :=
          Finset.sum_congr rfl fun σ _ => step σ
      _ = ∑ i, ∑ σ : Equiv.Perm n, ∑ j, w σ * ((σ.permMatrix ℝ) i j * (mu i * nu j)) :=
          Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ σ : Equiv.Perm n, w σ * ((σ.permMatrix ℝ) i j * (mu i * nu j)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, S i j * (mu i * nu j) := by
          subst hw
          simp [Matrix.sum_apply, Finset.sum_mul]
  rw [← hexp]
  calc ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i)
      ≤ ∑ σ' : Equiv.Perm n, w σ' * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left (hmono.sum_mul_comp_perm_le_sum_mul) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

#print axioms sum_doublyStochastic_mul_le

end Zeta23Redux.LinAlg

