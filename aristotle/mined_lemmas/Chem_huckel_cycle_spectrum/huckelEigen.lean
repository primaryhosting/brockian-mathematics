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

noncomputable def huckelEigen (n : ℕ) (k : Fin n) : ℂ :=
  2 * (Real.cos (2 * Real.pi * (k : ℕ) / n) : ℂ)

section

variable {n : ℕ} [NeZero n]

