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

theorem feit_thompson_primePow {G : Type u} [Group G] [Finite G] {p n : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ n) : IsSolvable G := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact isSolvable_of_isPGroup (p := p) (IsPGroup.of_card hcard)

/-- Unconditional base case: every finite group of squarefree order is solvable (all its Sylow
subgroups are cyclic, i.e. it is a Z-group).  In particular this covers all groups of odd
squarefree order. -/
