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

lemma c3root_ne_one : c3root ≠ 1 := by
  intro h
  have hre : c3root.re = Real.cos (2 * Real.pi / 3) := by
    rw [c3root, show (2 * (Real.pi : ℂ) * Complex.I / 3)
        = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  rw [h] at hre
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show (2 * Real.pi / 3) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  rw [hcos] at hre
  norm_num at hre

