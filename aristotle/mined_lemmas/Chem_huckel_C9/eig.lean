import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

noncomputable def eig (k : ZMod 9) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 9)

/-- The (unnormalised) discrete Fourier matrix, whose columns are the eigenvectors. -/
