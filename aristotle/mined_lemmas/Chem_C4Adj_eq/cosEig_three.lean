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

lemma cosEig_three : cosEig 3 = 0 := by
  have h : (2 * Real.pi * ((3 : ℕ) : ℝ) / 4 : ℝ) = Real.pi + Real.pi / 2 := by push_cast; ring
  have c : Real.cos (Real.pi + Real.pi / 2) = 0 := by rw [Real.cos_add]; simp
  rw [cosEig, show ((3 : Fin 4) : ℕ) = 3 from rfl, h, c]
  norm_num

