import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

theorem charpoly_C17adj :
    C17adj.charpoly =
      ∏ k : ZMod 17, (X - C ((2 * Real.cos (2 * Real.pi * k.val / 17) : ℝ) : ℂ)) := by
  have hA : C17adj = U17 * (D17 * V17) := by
    have := congrArg (fun M => M * V17) C17adj_mul_U17
    simp only [mul_assoc] at this
    rw [U17_mul_V17, mul_one] at this
    simpa [mul_assoc] using this
  have : C17adj.charpoly = D17.charpoly := by
    rw [hA, Matrix.charpoly_mul_comm, mul_assoc, V17_mul_U17, mul_one]
  rw [this, D17, Matrix.charpoly_diagonal]
  exact Finset.prod_congr rfl (fun k _ => by rw [ee_add_ee_neg k])

/-- **Hückel theory for `C₁₇`.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₇` factors as `∏_{k=0}^{16} (X - 2cos(2πk/17))`; i.e. the eigenvalues of `C₁₇` are
exactly `2 cos (2πk/17)`, `k = 0, …, 16`. -/
