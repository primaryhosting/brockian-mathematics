/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₄` (the Hückel matrix of cyclobutadiene
with `α = 0`, `β = 1`), viewed over `ℂ`. -/

noncomputable def huckelEig (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / 4)

