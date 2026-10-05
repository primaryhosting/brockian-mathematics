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

theorem zeta_geom_sum :
    1 + zeta + zeta ^ 2 + zeta ^ 3 + zeta ^ 4 + zeta ^ 5 + zeta ^ 6 = 0 := by
  have hne : zeta - 1 ≠ 0 := sub_ne_zero.mpr zeta_ne_one
  apply mul_left_cancel₀ hne
  rw [mul_zero]
  linear_combination zeta_pow_seven

/-- `2 cos(2πk/7)` expressed via the root of unity. -/
