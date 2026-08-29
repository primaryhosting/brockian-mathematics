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

lemma cosEig_two : cosEig 2 = -2 := by
  have h : (2 * Real.pi * ((2 : ℕ) : ℝ) / 4 : ℝ) = Real.pi := by push_cast; ring
  rw [cosEig, show ((2 : Fin 4) : ℕ) = 2 from rfl, h, Real.cos_pi]
  norm_num

