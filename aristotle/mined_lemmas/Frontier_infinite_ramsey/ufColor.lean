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

private def ufColor (C : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  if {m | C n m = true} ∈ hyperfilter ℕ then true else false

