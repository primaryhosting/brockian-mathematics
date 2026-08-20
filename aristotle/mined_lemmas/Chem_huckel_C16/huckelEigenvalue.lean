/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

noncomputable def huckelEigenvalue (k : Fin 16) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k : ℕ) / 16)

/-- The `k`-th Fourier node `ζ₁₆ᵏ`. -/
