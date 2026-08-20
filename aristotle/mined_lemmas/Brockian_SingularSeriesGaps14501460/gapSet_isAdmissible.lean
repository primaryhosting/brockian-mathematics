/-
# Singular Series Gaps 14501460 — Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps14501460.lean`.  The target theorem there is
stated in plain core Lean (its file has to start with a fixed header comment, which forbids
`import`s).  Here the same mathematical content is formalized in the idiomatic Mathlib way,
with tuples as `Finset ℤ`, primality as `Nat.Prime`, and residues in `ZMod p`.
-/

import Mathlib

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/

theorem gapSet_isAdmissible : IsAdmissible gapSet := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2
    exact ⟨1, by decide⟩
  by_cases h3 : p = 3
  · subst h3
    exact ⟨2, by decide⟩
  · have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have hp2 := hp.two_le
    refine exists_missing_residue (by omega) gapSet ?_
    rw [gapSet_card]
    omega

/-- Any admissible subset of the window `[1450, 1460]` has at most four elements: modulo `2`
and modulo `3` it must avoid one class each, and the surviving residues modulo `6` occur at
most twice among eleven consecutive integers. -/
