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

theorem five_le_of_prime {p : Nat} (hp : IsPrime p) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  have h4 : p ≠ 4 := by
    intro h
    rcases hp.2 2 (by omega : (2 : Nat) ∣ p) with h' | h' <;> omega
  have := hp.1
  omega

/-! ## The tuple `{1450, 1452, 1456, 1458}` is admissible -/

/-- Among the five values `0, 1, 2, 3, 4` at least one avoids any four prescribed integers. -/
