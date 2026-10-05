/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃` (every pair of distinct vertices
is adjacent). In Hückel theory this is the (shifted, scaled) Hamiltonian of the
cyclic three-carbon π-system. -/

lemma cos_two : 2 * Real.cos (2 * Real.pi * (2 : ℕ) / 3) = -1 := by
  have h : 2 * Real.pi * (2 : ℕ) / 3 = Real.pi + Real.pi / 3 := by
    push_cast; ring
  rw [h, Real.cos_add, Real.cos_pi_div_three, Real.sin_pi, Real.cos_pi]
  norm_num

