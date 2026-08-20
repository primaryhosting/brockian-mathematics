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

lemma huckelEig_one : huckelEig 1 = 0 := by
  have h : 2 * Real.pi * ((1 : ℕ) : ℝ) / 4 = Real.pi / 2 := by push_cast; ring
  rw [huckelEig, h, Real.cos_pi_div_two, mul_zero]

