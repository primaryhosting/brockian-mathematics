/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem esymm_two :
    (zeta ^ 1 + zeta ^ 6) * (zeta ^ 2 + zeta ^ 5) + (zeta ^ 1 + zeta ^ 6) * (zeta ^ 3 + zeta ^ 4)
      + (zeta ^ 2 + zeta ^ 5) * (zeta ^ 3 + zeta ^ 4) = -2 := by
  linear_combination (2 * zeta + 2 * zeta ^ 2 + zeta ^ 3 + zeta ^ 4) * zeta_pow_seven
    + 2 * zeta_geom_sum

/-- Elementary symmetric function of degree three of the three nontrivial eigenvalues. -/
