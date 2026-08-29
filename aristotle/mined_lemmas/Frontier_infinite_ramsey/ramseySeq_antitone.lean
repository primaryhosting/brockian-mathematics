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

private lemma ramseySeq_antitone {i j : ℕ} (h : i ≤ j) :
    ramseySeq C c0 j ⊆ ramseySeq C c0 i := by
  induction j with
  | zero => simpa using (Nat.le_zero.1 h) ▸ subset_rfl
  | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact (ramseySeq_succ_subset C c0 n).trans (ih (Nat.lt_succ_iff.1 hlt))
      · have : i = n + 1 := le_antisymm h hge
        subst this; exact subset_rfl

