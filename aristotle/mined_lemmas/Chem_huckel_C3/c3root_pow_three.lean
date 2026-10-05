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

lemma c3root_pow_three : c3root ^ 3 = 1 := by
  rw [c3root, ← Complex.exp_nat_mul]
  push_cast
  rw [show (3 : ℂ) * (2 * Real.pi * Complex.I / 3) = 2 * Real.pi * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

