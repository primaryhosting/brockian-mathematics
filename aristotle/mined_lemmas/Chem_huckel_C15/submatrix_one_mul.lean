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

lemma submatrix_one_mul (f g : Fin 15 → Fin 15) :
    ((1 : Matrix (Fin 15) (Fin 15) ℂ).submatrix f id) *
        ((1 : Matrix (Fin 15) (Fin 15) ℂ).submatrix g id)
      = (1 : Matrix (Fin 15) (Fin 15) ℂ).submatrix (g ∘ f) id := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id, Function.comp_apply]
  rw [Finset.sum_eq_single (f i)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

