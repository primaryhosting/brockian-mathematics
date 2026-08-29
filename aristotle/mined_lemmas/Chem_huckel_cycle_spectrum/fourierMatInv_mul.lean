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

lemma fourierMatInv_mul : fourierMatInv n * fourierMat n = 1 :=
  mul_eq_one_comm.1 (fourierMat_mul_inv n)

/-- `fourierMat` as a unit of the matrix ring. -/
