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

noncomputable def ev {n : ℕ} (a : Fin n) : ℂ := zeta n ^ (a : ℕ)

/-- The `k`-th Hückel π-energy (in units where α = 0, β = 1) of the cycle `C n`. -/
