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

lemma shift_pow (m : ℕ) :
    shift ^ m = (1 : Matrix (Fin 15) (Fin 15) ℂ).submatrix (fun i => i - Fin.ofNat 15 m) id := by
  induction m with
  | zero =>
      have h : (fun i : Fin 15 => i - Fin.ofNat 15 0) = id := by
        funext i; show i - 0 = i; simp
      rw [pow_zero, h, Matrix.submatrix_id_id]
  | succ m ih =>
      rw [pow_succ, ih, shift, submatrix_one_mul]
      congr 1
      funext i
      simp only [Function.comp_apply, ofNat_succ]
      abel

