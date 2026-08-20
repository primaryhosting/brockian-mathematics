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

/-- `ec n m = exp (2 π i m / n)`, an `n`-th root of unity raised to the power `m`. -/

lemma adjMatrix_mul_dft_eq {n : ℕ} (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).adjMatrix ℂ * dftMatrix n
      = dftMatrix n * Matrix.diagonal (fun k : Fin n => ((huckelEnergy n k.val : ℝ) : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  ext i k
  rw [adjMatrix_mul_dft (by omega) i k, Matrix.mul_diagonal, mul_comm]

/-- **Hückel theory for annulenes.** For `n ≥ 3`, the eigenvalues (spectrum) of the adjacency
matrix of the cycle graph `C n` are exactly the numbers `2 cos (2 π k / n)`, `k = 0, …, n - 1`.
In Hückel π-electron theory these are the orbital energies `α + 2 β cos (2 π k / n)` measured in
units of `β` relative to `α`.

The hypothesis `3 ≤ n` is necessary: in Mathlib `SimpleGraph.cycleGraph n` is a *simple* graph, so
for `n ≤ 2` it degenerates (`cycleGraph 1` has no edge and `cycleGraph 2` is a single edge rather
than a double edge) and the formula fails. -/
