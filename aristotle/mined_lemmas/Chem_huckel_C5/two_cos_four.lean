/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`):
vertices are indexed by `Fin 5` with cyclic successor `i ↦ i + 1`, and `i, j` are adjacent
iff one is the cyclic successor of the other. -/

lemma two_cos_four : 2 * Real.cos (2 * π * 4 / 5) = (√5 - 1) / 2 := by
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : (2 * π * 4 / 5) = 2 * π - 2 * (π / 5) := by ring
  rw [h, Real.cos_two_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

/-- The product `∏_{k<5} (X - 2cos(2πk/5))` equals `X⁵ - 5X³ + 5X - 2`. -/
