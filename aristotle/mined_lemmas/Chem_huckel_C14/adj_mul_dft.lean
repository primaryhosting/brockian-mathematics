/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

namespace Chem

open Complex Matrix

/-- The primitive 14-th root of unity `exp(2πi/14)`. -/

lemma adj_mul_dft :
    SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14) * dftMat
      = dftMat * Matrix.diagonal eigval := by
  ext j k
  have hL : (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14) * dftMat) j k
      = ∑ m ∈ (SimpleGraph.cycleGraph 14).neighborFinset j, dftMat m k := by
    rw [show (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14) * dftMat) j k
        = (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14) *ᵥ fun m => dftMat m k) j from rfl,
      SimpleGraph.adjMatrix_mulVec_apply]
  rw [hL, cycle14_neighborFinset, Finset.sum_pair (fin14_pred_ne_succ j),
    Matrix.mul_diagonal, dftMat_apply, dftMat_apply, dftMat_apply, eigval_eq, mul_add,
    ← zpow_add₀ om_ne_zero, ← zpow_add₀ om_ne_zero]
  have e2 : om ^ ((((j - 1).val * k.val : ℕ)) : ℤ)
      = om ^ (((j.val * k.val : ℕ) : ℤ) + -(k.val : ℤ)) := by
    refine om_zpow_eq ?_
    have hq : ((j - 1).val : ℕ) = (j.val + 13) % 14 := by simp [Fin.sub_def]; omega
    have h : (14 : ℤ) ∣ (((j - 1).val : ℤ) - (j.val : ℤ) + 1) := by
      have hj := j.isLt; omega
    obtain ⟨c, hc⟩ := h
    refine ⟨c * k.val, ?_⟩
    push_cast
    nlinarith [hc]
  have e1 : om ^ ((((j + 1).val * k.val : ℕ)) : ℤ)
      = om ^ (((j.val * k.val : ℕ) : ℤ) + (k.val : ℤ)) := by
    refine om_zpow_eq ?_
    have hp : ((j + 1).val : ℕ) = (j.val + 1) % 14 := by simp [Fin.add_def]
    have h : (14 : ℤ) ∣ (((j + 1).val : ℤ) - (j.val : ℤ) - 1) := by
      have hj := j.isLt; omega
    obtain ⟨c, hc⟩ := h
    refine ⟨c * k.val, ?_⟩
    push_cast
    nlinarith [hc]
  rw [e1, e2, add_comm]

