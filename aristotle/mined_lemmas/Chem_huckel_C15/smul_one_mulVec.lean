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

lemma smul_one_mulVec (c : ℂ) (v : Fin 15 → ℂ) (i : Fin 15) :
    ((c • (1 : Matrix (Fin 15) (Fin 15) ℂ)) *ᵥ v) i = c * v i := by
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Finset.sum_ite_eq]

/-- Every 15-th root of unity is an eigenvalue of the cyclic shift matrix:
the vector `i ↦ ν ^ i` is an eigenvector for the eigenvalue `ν¹⁴ = ν⁻¹`. -/
