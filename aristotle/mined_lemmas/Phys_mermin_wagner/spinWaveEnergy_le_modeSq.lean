/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Real

namespace Phys

/-- The spin-wave (harmonic) energy of the Fourier mode `j` of a nearest-neighbour
model on the `d`-dimensional discrete torus with `L` sites per side, in units where
the coupling constant is `1`.  The momentum attached to the mode `j` has components
`k i = 2π * j i / L`, and the lattice dispersion relation is
`ε k = ∑ i, 2 * (1 - cos (k i))`. -/

lemma spinWaveEnergy_le_modeSq (d L : ℕ) (j : Fin d → Fin L) :
    spinWaveEnergy d L j ≤ modeSq d L j := by
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Real.one_sub_sq_div_two_le_cos (x := 2 * π * ((j i : ℕ) : ℝ) / (L : ℝ))
  linarith

/-- A nonzero mode has strictly positive squared momentum. -/
