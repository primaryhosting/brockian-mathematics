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

namespace Zeta23Redux.LinAlg

open Finset

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

omit [Fintype n] [DecidableEq n] in
/-- Two antitone sequences monovary. -/
lemma monovary_of_antitone {mu nu : n → ℝ} (hmu : Antitone mu) (hnu : Antitone nu) :
    Monovary mu nu := by
  intro i j hij
  have hji : j < i := by
    by_contra h
    exact absurd (hnu (not_lt.1 h)) (not_le.2 hij)
  exact hmu hji.le

omit [LinearOrder n] in
/-- Expanding the bilinear form against a permutation matrix. -/
lemma sum_permMatrix_mul (sigma : Equiv.Perm n) (mu nu : n → ℝ) :
    ∑ i, ∑ j, (sigma.permMatrix ℝ) i j * (mu i * nu j) = ∑ i, mu i * nu (sigma i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.toPEquiv, ite_mul]

/-- For a doubly stochastic matrix `S` and antitone weight sequences `mu`, `nu`,
the bilinear form `∑ i, ∑ j, S i j * (mu i * nu j)` is at most `∑ i, mu i * nu i`.
This is the rearrangement/Birkhoff step feeding the von Neumann trace inequality. -/
theorem sum_doublyStochastic_mul_le {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n)
    {mu nu : n → ℝ} (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  have hmono : Monovary mu nu := monovary_of_antitone hmu hnu
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hexp : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ sigma : Equiv.Perm n, w sigma * ∑ i, mu i * nu (sigma i) := by
    have step : ∀ sigma : Equiv.Perm n, w sigma * ∑ i, mu i * nu (sigma i)
        = ∑ i, ∑ j, (w sigma * (sigma.permMatrix ℝ) i j) * (mu i * nu j) := by
      intro sigma
      rw [← sum_permMatrix_mul sigma mu nu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← hwS]
    simp only [step]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.sum_apply, Finset.sum_mul]
  rw [hexp]
  calc ∑ sigma : Equiv.Perm n, w sigma * ∑ i, mu i * nu (sigma i)
      ≤ ∑ _sigma : Equiv.Perm n, w _sigma * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun sigma _ => ?_
        exact mul_le_mul_of_nonneg_left (hmono.sum_mul_comp_perm_le_sum_mul) (hw0 sigma)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

end Zeta23Redux.LinAlg

