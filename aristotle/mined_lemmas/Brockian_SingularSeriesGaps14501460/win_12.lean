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

theorem win_12 (x : Int) (h1 : 1450 ≤ x) (h2 : x ≤ 1460) (h3 : x % 2 ≠ 1) (h4 : x % 3 ≠ 2) :
    x = 1450 ∨ x = 1452 ∨ x = 1456 ∨ x = 1458 := by omega

/-- No admissible tuple of five distinct integers fits inside the range `[1450, 1460]`. -/
