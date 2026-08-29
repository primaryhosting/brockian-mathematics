/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib (as of this version) contains no infinite Ramsey theorem — searching for `Ramsey`
turns up only `Mathlib/Combinatorics/Hindman.lean` and `Mathlib/Combinatorics/HalesJewett.lean`,
where the word occurs in comments.  So we prove it from scratch, using the classical
ultrafilter argument based on `Filter.hyperfilter`.
-/

namespace Frontier

open Filter Set

noncomputable section

/-- A choice of element of a set of naturals (junk value `0` for the empty set). -/

private def ramseySeq : ℕ → Set ℕ
  | 0 => {n | ufColor C n = c0}
  | k + 1 =>
      (ramseySeq k) ∩ Ioi (pick (ramseySeq k)) ∩ {m | C (pick (ramseySeq k)) m = c0}

/-- The `k`-th element of the monochromatic set. -/
