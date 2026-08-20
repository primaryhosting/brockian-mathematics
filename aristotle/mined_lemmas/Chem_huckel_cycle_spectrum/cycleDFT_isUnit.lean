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

lemma cycleDFT_isUnit (m : ℕ) : IsUnit (cycleDFT (m + 3)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [cycleDFT, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne fun h => ?_
  have hval : (j : ℕ) = (i : ℕ) :=
    (cycleRoot_isPrimitiveRoot (n := m + 3) (by omega)).pow_inj j.isLt i.isLt h
  exact hj.ne' (Fin.ext hval)

/-- The characteristic polynomial of the Hückel (adjacency) matrix of the cycle `C n`,
for `n ≥ 3`, is `∏ k, (X - 2 cos (2 π k / n))`. -/
