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

theorem cubic_factor (l : ℂ) :
    l ^ 3 + l ^ 2 - 2 * l - 1 =
      (l - (zeta ^ 1 + zeta ^ 6)) * (l - (zeta ^ 2 + zeta ^ 5)) * (l - (zeta ^ 3 + zeta ^ 4)) := by
  linear_combination (l ^ 2 : ℂ) * esymm_one - l * esymm_two + esymm_three

/-! ### Main theorem -/

/-- **Hückel theory for the cycle `C₇`.**  A complex number `l` is an eigenvalue of the
adjacency matrix of the cycle graph `C₇` (i.e. there is a nonzero vector `v` with `A v = l v`)
if and only if `l = 2 cos(2πk/7)` for some `k ∈ {0, 1, …, 6}`. -/
