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

theorem esymm_three :
    (zeta ^ 1 + zeta ^ 6) * (zeta ^ 2 + zeta ^ 5) * (zeta ^ 3 + zeta ^ 4) = 1 := by
  linear_combination (zeta ^ 7 + zeta ^ 8 + zeta ^ 5 + zeta ^ 4 + zeta ^ 3 + zeta ^ 2 + zeta + 2)
    * zeta_pow_seven + zeta_geom_sum

/-- The cubic `x³ + x² - 2x - 1` factors over the three nontrivial eigenvalues. -/
