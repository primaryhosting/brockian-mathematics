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

theorem five_in_four {a b c d e v1 v2 v3 v4 : Int}
    (ha : a = v1 ∨ a = v2 ∨ a = v3 ∨ a = v4)
    (hb : b = v1 ∨ b = v2 ∨ b = v3 ∨ b = v4)
    (hc : c = v1 ∨ c = v2 ∨ c = v3 ∨ c = v4)
    (hd : d = v1 ∨ d = v2 ∨ d = v3 ∨ d = v4)
    (he : e = v1 ∨ e = v2 ∨ e = v3 ∨ e = v4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : False := by
  omega

