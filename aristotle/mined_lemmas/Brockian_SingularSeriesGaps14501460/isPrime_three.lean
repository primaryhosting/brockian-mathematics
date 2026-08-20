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

theorem isPrime_three : IsPrime 3 := by
  refine ⟨by omega, fun m hm => ?_⟩
  have h1 : m ≤ 3 := Nat.le_of_dvd (by omega) hm
  have h2 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases h2 with rfl | rfl | rfl | rfl
  · exact absurd hm (by decide)
  · exact Or.inl rfl
  · exact absurd hm (by decide)
  · exact Or.inr rfl

/-- A prime other than `2` and `3` is at least `5`. -/
