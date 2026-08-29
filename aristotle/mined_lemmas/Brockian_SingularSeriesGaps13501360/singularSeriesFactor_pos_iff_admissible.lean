/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Finset

/-- A finite set of integers is *admissible* if, for every prime `p`, it fails to cover
all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series of the tuple is nonzero. -/

theorem singularSeriesFactor_pos_iff_admissible (d : ℤ) (hd : d ≠ 0) :
    0 < singularSeriesFactor d ↔ Admissible {0, d} := by
  rw [admissible_pair_iff d hd]
  constructor
  · intro h
    by_contra hodd
    rw [singularSeriesFactor_eq_zero_of_odd hodd] at h
    exact lt_irrefl _ h
  · intro hev
    exact singularSeriesFactor_pos_of_even hev hd

end Basic

/-- **Singular series gaps in the range 1350–1360.**
For every gap `d` in the range `1350 ≤ d ≤ 1360`, the pair `{0, d}` is admissible – equivalently,
the singular series factor `𝔖(d)` is positive – precisely when `d` is even; and for odd `d`
in this range the pair is inadmissible and the singular series factor vanishes.
The admissible gaps in this range are therefore exactly
`1350, 1352, 1354, 1356, 1358, 1360`. -/
