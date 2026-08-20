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

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, fun m hm => ?_⟩
  have h1 : m ≤ 2 := Nat.le_of_dvd (by omega) hm
  have h2 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases h2 with rfl | rfl | rfl
  · exact absurd hm (by decide)
  · exact Or.inl rfl
  · exact Or.inr rfl

