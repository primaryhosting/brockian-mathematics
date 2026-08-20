import Mathlib

/-!
# Hückel spectrum of the cycle graph `C₁₅`

The eigenvalues of the adjacency matrix of the cycle graph `C₁₅` (the Hückel spectrum of a
15-membered annulene, in units of β above α) are exactly the numbers `2 cos (2πk/15)`
for `k = 0, …, 14`.

The proof writes the adjacency matrix as `S + S¹⁴`, where `S` is the cyclic shift permutation
matrix, identifies the spectrum of `S` with the set of 15-th roots of unity, and then applies
the polynomial spectral mapping theorem over `ℂ`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The cyclic shift permutation matrix on `Fin 15`: `shift i j = 1` iff `i - 1 = j`. -/

lemma adjMatrix_eq : (SimpleGraph.cycleGraph 15).adjMatrix ℂ = shift + shift ^ 14 := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply, Matrix.add_apply, shift_apply, shift_pow_apply]
  have h14 : Fin.ofNat 15 14 = 14 := rfl
  rw [h14]
  simp only [SimpleGraph.cycleGraph_adj]
  by_cases h1 : i - 1 = j <;> by_cases h2 : i - 14 = j <;> simp [h1, h2] <;> omega

