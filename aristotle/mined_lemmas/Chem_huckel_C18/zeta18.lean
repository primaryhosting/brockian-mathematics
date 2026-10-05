/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

noncomputable def zeta18 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

/-- The Hückel energies of the cycle `C₁₈` (in units of `β`, with `α = 0`):
`2 cos (2πk/18)` for `k = 0, …, 17`. -/
