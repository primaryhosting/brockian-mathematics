/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

noncomputable def zeta16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The Fourier (Vandermonde) matrix diagonalizing `C16`. -/
