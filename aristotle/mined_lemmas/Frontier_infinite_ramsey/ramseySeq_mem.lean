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

private lemma ramseySeq_mem (h0 : {n | ufColor C n = c0} ∈ hyperfilter ℕ) (k : ℕ) :
    ramseySeq C c0 k ∈ hyperfilter ℕ := by
  induction k with
  | zero => simpa [ramseySeq] using h0
  | succ n ih =>
      have hne : (ramseySeq C c0 n).Nonempty := Ultrafilter.nonempty_of_mem ih
      have hx : pick (ramseySeq C c0 n) ∈ ramseySeq C c0 n := pick_mem hne
      set x := pick (ramseySeq C c0 n) with hxdef
      have hx0 : x ∈ ramseySeq C c0 0 := ramseySeq_antitone C c0 (Nat.zero_le n) hx
      have hcol : ufColor C x = c0 := hx0
      have h1 : Ioi x ∈ hyperfilter ℕ := by
        refine mem_hyperfilter_of_finite_compl ?_
        simpa using (Set.finite_Iic x)
      have h2 : {m | C x m = c0} ∈ hyperfilter ℕ := by
        have := ufColor_mem C x
        rwa [hcol] at this
      have : ramseySeq C c0 n ∩ Ioi x ∩ {m | C x m = c0} ∈ hyperfilter ℕ :=
        Ultrafilter.inter_mem (Ultrafilter.inter_mem ih h1) h2
      simpa [ramseySeq, ← hxdef] using this

