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

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

lemma eigenvalue_quartic {μ : ℝ} {v : Fin 6 → ℝ} (hv : v ≠ 0) (h : A6 *ᵥ v = μ • v) :
    μ ^ 4 - 5 * μ ^ 2 + 4 = 0 := by
  have hB : B6 *ᵥ v = (μ ^ 2) • v := by
    rw [← A6_mul_A6, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul]
    ring_nf
  have hBB : (B6 * B6) *ᵥ v = (μ ^ 4) • v := by
    rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_smul, hB, smul_smul]
    ring_nf
  rw [B6_mul_B6] at hBB
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hB, Matrix.one_mulVec,
    smul_smul] at hBB
  have hzero : (μ ^ 4 - 5 * μ ^ 2 + 4) • v = 0 := by
    rw [add_smul, sub_smul, ← hBB]
    abel
  rcases smul_eq_zero.mp hzero with h' | h'
  · exact h'
  · exact absurd h' hv

/-- The values `2 cos (2πk/6)`, `k = 0,…,5`, are exactly `2, 1, -1, -2`. -/
