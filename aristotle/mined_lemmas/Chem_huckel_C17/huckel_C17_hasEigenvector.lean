import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

theorem huckel_C17_hasEigenvector (k : ZMod 17) :
    (fun j => ee (j * k)) ≠ (0 : ZMod 17 → ℂ) ∧
      C17adj.mulVec (fun j => ee (j * k))
        = ((2 * Real.cos (2 * Real.pi * k.val / 17) : ℝ) : ℂ) • (fun j => ee (j * k)) := by
  constructor
  · intro h
    have h0 : ee (0 * k) = 0 := congrFun h 0
    rw [zero_mul, ee_zero] at h0
    exact one_ne_zero h0
  · funext i
    have hcol := congrFun (congrFun C17adj_mul_U17 i) k
    rw [Matrix.mul_apply, Matrix.mul_apply] at hcol
    have hright : ∑ j : ZMod 17, U17 i j * D17 j k = ee (i * k) * (ee k + ee (-k)) := by
      simp [D17, U17, Matrix.diagonal_apply, Finset.sum_ite_eq', mul_comm]
    rw [hright] at hcol
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [← ee_add_ee_neg k, mul_comm (ee k + ee (-k)) (ee (i * k)), ← hcol]
    exact Finset.sum_congr rfl (fun j _ => by simp [U17])

end Chem

#print axioms Chem.huckel_C17
#print axioms Chem.huckel_C17_roots
#print axioms Chem.huckel_C17_hasEigenvector

