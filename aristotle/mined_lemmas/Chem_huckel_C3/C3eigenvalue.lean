/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
in units where `α = 0` and `β = 1`). -/

noncomputable def C3eigenvalue (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / 3)

