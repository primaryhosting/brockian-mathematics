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

/-!
# Hückel spectrum of the cycle `C₁₅`

The adjacency matrix of the cycle graph `C₁₅` has characteristic polynomial
`∏_{k=0}^{14} (X - 2cos(2πk/15))`; equivalently its eigenvalues are the numbers
`2cos(2πk/15)` for `k = 0, …, 14`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- A primitive 15-th root of unity. -/

theorem huckel_C15_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 15).adjMatrix ℂ) =
      {z : ℂ | ∃ k : ℕ, k < 15 ∧ z = ((2 * Real.cos (2 * Real.pi * k / 15) : ℝ) : ℂ)} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C15]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_range,
    sub_eq_zero, Set.mem_setOf_eq]

end Chem

