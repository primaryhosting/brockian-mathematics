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

lemma two_cos_four_pi_div_five : 2 * Real.cos (4 * π / 5) = -(1 + Real.sqrt 5) / 2 := by
  have h : (4 : ℝ) * π / 5 = π - π / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

/-- The adjacency matrix of `C₅` satisfies the polynomial
`x³ - x² - 3x + 2 = (x - 2)(x² + x - 1)`. -/
