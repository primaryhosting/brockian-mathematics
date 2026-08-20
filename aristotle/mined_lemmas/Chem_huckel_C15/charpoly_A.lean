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

theorem charpoly_A : A.charpoly = ∏ k : Fin 15, (X - C (hlevel k.val)) := by
  rw [A_eq_conj, Matrix.charpoly_units_conj, D, Matrix.charpoly_diagonal]

/-- **Hückel theory for the annulene `C₁₅`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₅` is `∏_{k=0}^{14} (X - 2·cos(2πk/15))`, i.e. the adjacency
eigenvalues of `C₁₅` are exactly `2·cos(2πk/15)` for `k = 0, …, 14` (with multiplicity). -/
