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

theorem exists_small_avoiding (x1 x2 x3 x4 : Int) :
    ∃ r : Int, 0 ≤ r ∧ r < 5 ∧ x1 ≠ r ∧ x2 ≠ r ∧ x3 ≠ r ∧ x4 ≠ r := by
  by_cases h0 : x1 ≠ 0 ∧ x2 ≠ 0 ∧ x3 ≠ 0 ∧ x4 ≠ 0
  · exact ⟨0, by omega⟩
  by_cases h1 : x1 ≠ 1 ∧ x2 ≠ 1 ∧ x3 ≠ 1 ∧ x4 ≠ 1
  · exact ⟨1, by omega⟩
  by_cases h2 : x1 ≠ 2 ∧ x2 ≠ 2 ∧ x3 ≠ 2 ∧ x4 ≠ 2
  · exact ⟨2, by omega⟩
  by_cases h3 : x1 ≠ 3 ∧ x2 ≠ 3 ∧ x3 ≠ 3 ∧ x4 ≠ 3
  · exact ⟨3, by omega⟩
  by_cases h4 : x1 ≠ 4 ∧ x2 ≠ 4 ∧ x3 ≠ 4 ∧ x4 ≠ 4
  · exact ⟨4, by omega⟩
  · exact ((by omega : False)).elim

/-- Four integers cannot meet every residue class modulo a modulus `p ≥ 5`. -/
