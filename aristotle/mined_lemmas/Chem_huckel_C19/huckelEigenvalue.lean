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

noncomputable def huckelEigenvalue (k : ℕ) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)

/-- The (unnormalised) discrete Fourier matrix; its `k`-th column is the eigenvector
of `C19adj` for the eigenvalue `2 cos (2πk/19)`. -/
