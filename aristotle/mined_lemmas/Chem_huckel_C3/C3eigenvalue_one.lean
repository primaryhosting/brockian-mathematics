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

lemma C3eigenvalue_one : C3eigenvalue 1 = -1 := by
  have h : (2 * Real.pi * (1 : ℕ) / 3) = Real.pi - Real.pi / 3 := by push_cast; ring
  simp only [C3eigenvalue, h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

