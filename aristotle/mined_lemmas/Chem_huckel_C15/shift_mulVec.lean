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

lemma shift_mulVec (v : Fin 15 → ℂ) (i : Fin 15) : (shift *ᵥ v) i = v (i - 1) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (i - 1)]
  · simp [shift_apply]
  · intro b _ hb; simp [shift_apply, Ne.symm hb]
  · simp

