/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/

lemma sum_bilinear_le_of_doublyStochastic {mu nu : n → ℝ} (h : Monovary mu nu)
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hSij : ∀ i j, S i j = ∑ sg : Equiv.Perm n, (if sg i = j then w sg else 0) := by
    intro i j
    rw [← hw]
    simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have key : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ sg : Equiv.Perm n, w sg * ∑ i, mu i * nu (sg i) := by
    have step : ∀ i : n, ∑ j, S i j * (mu i * nu j)
        = ∑ sg : Equiv.Perm n, w sg * (mu i * nu (sg i)) := by
      intro i
      simp only [hSij, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun sg _ => ?_
      simp
    simp only [step]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun sg _ => by rw [Finset.mul_sum]
  rw [key]
  calc ∑ sg : Equiv.Perm n, w sg * ∑ i, mu i * nu (sg i)
      ≤ ∑ _sg : Equiv.Perm n, w _sg * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun sg _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (hw0 sg)
        simpa [smul_eq_mul] using h.sum_smul_comp_perm_le_sum_smul (σ := sg)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Entrywise expansion of the trace of `Wᴴ Dₐ W D_b`. -/
