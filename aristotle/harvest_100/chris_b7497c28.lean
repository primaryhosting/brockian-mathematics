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

/-!
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Matrix

namespace Zeta23Redux.LinAlg

/-- For a permutation matrix, the double sum `∑ i ∑ j, P i j * (μ i * ν j)` collapses to
`∑ i, μ i * ν (σ i)`. -/
lemma sum_permMatrix_mul {n : Type*} [Fintype n] [DecidableEq n] (sigma : Equiv.Perm n)
    (mu nu : n → ℝ) :
    ∑ i, ∑ j, (sigma.permMatrix ℝ) i j * (mu i * nu j) = ∑ i, mu i * nu (sigma i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-- **Rearrangement / Birkhoff step for the von Neumann trace inequality.**
If `S` is doubly stochastic and the weight sequences `mu`, `nu` are antitone, then
`∑ i ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i`. -/
theorem sum_doublyStochastic_mul_le {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) {mu nu : n → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hmono : Monovary mu nu := hmu.monovary hnu
  have hentry : ∀ i j, S i j = ∑ sigma : Equiv.Perm n, w sigma * (sigma.permMatrix ℝ) i j := by
    intro i j
    rw [← hwS]
    simp [Finset.sum_apply]
  have hexp : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ sigma : Equiv.Perm n, w sigma * ∑ i, mu i * nu (sigma i) := by
    have : ∀ i j, S i j * (mu i * nu j)
        = ∑ sigma : Equiv.Perm n, w sigma * ((sigma.permMatrix ℝ) i j * (mu i * nu j)) := by
      intro i j
      rw [hentry i j, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have swap : ∀ i : n, ∑ j, ∑ sigma : Equiv.Perm n,
        w sigma * ((sigma.permMatrix ℝ) i j * (mu i * nu j))
        = ∑ sigma : Equiv.Perm n, ∑ j,
          w sigma * ((sigma.permMatrix ℝ) i j * (mu i * nu j)) := fun _ => Finset.sum_comm
    simp only [this, swap]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun sigma _ => ?_
    rw [← sum_permMatrix_mul sigma mu nu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  rw [hexp]
  calc ∑ sigma : Equiv.Perm n, w sigma * ∑ i, mu i * nu (sigma i)
      ≤ ∑ _sigma : Equiv.Perm n, w _sigma * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun sigma _ =>
          mul_le_mul_of_nonneg_left hmono.sum_mul_comp_perm_le_sum_mul (hw0 sigma)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

end Zeta23Redux.LinAlg

