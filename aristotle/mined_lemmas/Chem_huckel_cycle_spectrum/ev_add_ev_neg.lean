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

lemma ev_add_ev_neg (a : Fin n) : ev a + ev (-a) = huckelEigen n a := by
  have hexp : ev a = Complex.exp ((2 * Real.pi * (a : ℕ) / n : ℝ) * Complex.I) := by
    rw [ev, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hexp' : ev (-a) = Complex.exp (-((2 * Real.pi * (a : ℕ) / n : ℝ) * Complex.I)) := by
    rw [ev_neg, hexp, Complex.exp_neg]
  rw [hexp, hexp', huckelEigen, ← Complex.ofReal_cos, Complex.cos]
  push_cast
  ring

end

section Matrices

variable (n : ℕ) [NeZero n]

/-- The (unnormalised) discrete Fourier matrix, whose `k`-th column is the eigenvector of the
cycle adjacency matrix for the eigenvalue `huckelEigen n k`. -/
