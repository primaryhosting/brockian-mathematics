/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

def hval (k : ZMod 18) : ℂ := ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ)

/-- The (unnormalized) discrete Fourier matrix. -/
