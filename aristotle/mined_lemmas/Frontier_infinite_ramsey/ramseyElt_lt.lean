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

private lemma ramseyElt_lt (h0 : {n | ufColor C n = c0} ∈ hyperfilter ℕ) (k : ℕ) :
    ramseyElt C c0 k < ramseyElt C c0 (k + 1) := by
  have h := ramseyElt_mem C c0 h0 (k + 1)
  have : ramseyElt C c0 (k + 1) ∈ Ioi (pick (ramseySeq C c0 k)) := h.1.2
  simpa [ramseyElt] using this

