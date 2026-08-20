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

noncomputable def zeta16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of cyclic C₁₆,
with `α = 0`, `β = 1`). -/
