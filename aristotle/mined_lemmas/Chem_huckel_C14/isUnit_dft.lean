import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma isUnit_dft : IsUnit dft := IsUnit.of_mul_eq_one dftInv dft_mul_dftInv

/-- **Hückel theory for `C₁₄`**: the eigenvalues (spectrum) of the adjacency matrix of the
cycle graph `C₁₄` are exactly `2 cos (2πk/14)` for `k = 0, …, 13`. -/
