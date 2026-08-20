/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)

/-- The adjacency matrix of the cycle graph `C₁₉` (the Hückel matrix of the
19-membered annulene, in units where `α = 0` and `β = 1`). -/
