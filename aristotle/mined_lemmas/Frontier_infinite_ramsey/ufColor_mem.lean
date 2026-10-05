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

private lemma ufColor_mem (C : ℕ → ℕ → Bool) (n : ℕ) :
    {m | C n m = ufColor C n} ∈ hyperfilter ℕ := by
  by_cases h : {m | C n m = true} ∈ hyperfilter ℕ
  · simpa [ufColor, h] using h
  · have hc : {m | C n m = true}ᶜ ∈ hyperfilter ℕ :=
      (Ultrafilter.compl_mem_iff_notMem).2 h
    have he : {m | C n m = false} = {m | C n m = true}ᶜ := by
      ext m; simp [Bool.eq_false_iff]
    simpa [ufColor, h, he] using hc

variable (C : ℕ → ℕ → Bool) (c0 : Bool)

/-- The decreasing sequence of large sets used to build the monochromatic set. -/
