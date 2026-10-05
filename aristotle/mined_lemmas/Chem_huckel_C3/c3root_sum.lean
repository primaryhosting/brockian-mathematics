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

lemma c3root_sum : 1 + c3root + c3root ^ 2 = 0 := by
  have hne : c3root - 1 ≠ 0 := sub_ne_zero.mpr c3root_ne_one
  have hprod : (c3root - 1) * (1 + c3root + c3root ^ 2) = 0 := by
    linear_combination c3root_pow_three
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd h hne
  · exact h

/-- The adjacency matrix of `C₃`, viewed over `ℂ`. -/
