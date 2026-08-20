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

lemma shift_pow_fifteen : shift ^ 15 = 1 := by
  have h : (fun i : Fin 15 => i - Fin.ofNat 15 15) = id := by
    funext i; show i - 0 = i; simp
  rw [shift_pow, h, Matrix.submatrix_id_id]

/-- The adjacency matrix of `C₁₅` is `S + S¹⁴ = S + S⁻¹` for the cyclic shift `S`. -/
