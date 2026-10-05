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

lemma two_cos_three : 2 * Real.cos (2 * π * 3 / 5) = -(1 + √5) / 2 := by
  have h : (2 * π * 3 / 5) = π + π / 5 := by ring
  rw [h, Real.cos_add, Real.cos_pi_div_five]
  simp
  ring

