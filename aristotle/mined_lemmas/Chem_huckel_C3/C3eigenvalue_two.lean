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

lemma C3eigenvalue_two : C3eigenvalue 2 = -1 := by
  have h : (2 * Real.pi * (2 : ℕ) / 3) = Real.pi + Real.pi / 3 := by push_cast; ring
  simp only [C3eigenvalue, h, Real.cos_add, Real.cos_pi, Real.sin_pi,
    Real.cos_pi_div_three]
  norm_num

/-- **Hückel theory for the cyclopropenyl system.**
A real number `x` is an eigenvalue of the adjacency matrix of the cycle graph `C₃`
if and only if it is of the form `2·cos(2πk/3)` for some `k ∈ {0, 1, 2}`. -/
