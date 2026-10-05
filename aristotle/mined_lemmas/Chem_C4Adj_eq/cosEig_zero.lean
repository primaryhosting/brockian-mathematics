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

lemma cosEig_zero : cosEig 0 = 2 := by
  have h : (2 * Real.pi * ((0 : ℕ) : ℝ) / 4 : ℝ) = 0 := by push_cast; ring
  rw [cosEig, show ((0 : Fin 4) : ℕ) = 0 from rfl, h, Real.cos_zero]
  norm_num

