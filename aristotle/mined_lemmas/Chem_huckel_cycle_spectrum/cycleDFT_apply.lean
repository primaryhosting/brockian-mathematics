import Mathlib

/-!
# Hückel π-energies of the cycle graph `C n`

The adjacency (Hückel) matrix of the cycle graph `C n` (`n ≥ 3`) has spectrum
`{2 cos (2 π k / n) : k = 0, …, n-1}`, and its characteristic polynomial is
`∏ k, (X - 2 cos (2 π k / n))`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma cycleDFT_apply (n : ℕ) (i k : Fin n) :
    cycleDFT n i k = cycleRoot n ^ ((i : ℕ) * (k : ℕ)) := by
  simp [cycleDFT, Matrix.vandermonde, pow_mul]

