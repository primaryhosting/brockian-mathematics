/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix

namespace Chem

/-- The adjacency matrix (Hückel matrix with `α = 0`, `β = 1`) of the cycle graph `C₄`. -/

noncomputable def cosEig (k : Fin 4) : ℂ := ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) : ℝ) : ℂ)

