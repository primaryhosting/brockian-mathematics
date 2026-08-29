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

lemma cos_one : 2 * Real.cos (2 * Real.pi * (1 : ℕ) / 3) = -1 := by
  have h : 2 * Real.pi * (1 : ℕ) / 3 = Real.pi - Real.pi / 3 := by
    push_cast; ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

