/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because a module docstring is a
-- command and Lean 4 requires `import` lines to precede every command in a file.)

import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace Frontier

/-- The "simple-group input" of the Feit–Thompson theorem, in universe `u`:
every finite **simple** group of odd order is abelian (equivalently, of prime order). -/

theorem feit_thompson_squarefree {G : Type u} [Group G] [Finite G]
    (hcard : Squarefree (Nat.card G)) : IsSolvable G :=
  have : IsZGroup G := IsZGroup.of_squarefree hcard
  inferInstance

/-- A sharpened simple-group input: it suffices to rule out nonabelian finite simple groups of
odd order whose order is neither a prime power nor squarefree. -/
