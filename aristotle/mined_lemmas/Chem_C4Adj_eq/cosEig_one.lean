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

lemma cosEig_one : cosEig 1 = 0 := by
  have h : (2 * Real.pi * ((1 : ℕ) : ℝ) / 4 : ℝ) = Real.pi / 2 := by push_cast; ring
  rw [cosEig, show ((1 : Fin 4) : ℕ) = 1 from rfl, h, Real.cos_pi_div_two]
  norm_num

