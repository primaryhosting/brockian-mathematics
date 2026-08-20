/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Real

/-- The adjacency matrix of the cycle graph `C₅`, on vertex set `Fin 5` with the
cyclic (mod 5) neighbour relation. In Hückel theory (with `α = 0`, `β = 1`) this is the
Hückel matrix of the cyclic π-system of `C₅`. -/

lemma two_cos_two_pi_div_five : 2 * Real.cos (2 * π / 5) = (Real.sqrt 5 - 1) / 2 := by
  have h : (2 : ℝ) * π / 5 = 2 * (π / 5) := by ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

/-- `2 cos(4π/5) = -(1 + √5)/2`. -/
