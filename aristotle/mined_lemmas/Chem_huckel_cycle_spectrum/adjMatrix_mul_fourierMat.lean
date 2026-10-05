/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Polynomial Matrix SimpleGraph Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma adjMatrix_mul_fourierMat :
    ((cycleGraph (m + 3)).adjMatrix ℂ) * fourierMat (m + 3)
      = fourierMat (m + 3) * Matrix.diagonal (huckelEigen (m + 3)) := by
  ext i k
  rw [Matrix.mul_apply, cycle_adj_sum (fun j => fourierMat (m + 3) j k) i,
    Matrix.mul_diagonal]
  simp only [fourierMat]
  rw [show (i - 1) * k = i * k + -(1 * k) by ring, show (i + 1) * k = i * k + 1 * k by ring,
    ev_add, ev_add, one_mul, ← mul_add, ← ev_add_ev_neg k]
  ring

end Cycle

/-- **Hückel spectrum of the cycle graph.**  For `n ≥ 3`, the characteristic polynomial of the
adjacency matrix of the cycle graph `C n` factors as `∏ k, (X - 2cos(2πk/n))`, and consequently
its spectrum (set of eigenvalues) is exactly `{2cos(2πk/n) : k = 0, …, n-1}` — the Hückel
π-energies of the cyclic polyene. -/
