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

theorem gapTuple_admissible : Admissible gapTuple := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2
    exact ⟨1451, by decide⟩
  by_cases h3 : p = 3
  · subst h3
    exact ⟨1451, by decide⟩
  · have h5 : (5 : Int) ≤ (p : Int) := by
      have := five_le_of_prime hp h2 h3
      omega
    exact exists_residue_of_five_le (p : Int) h5 1450 1452 1456 1458

