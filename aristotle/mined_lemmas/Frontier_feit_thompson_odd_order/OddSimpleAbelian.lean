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

def OddSimpleAbelian : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Odd (Nat.card G) → IsSimpleGroup G → ∀ a b : G, a * b = b * a

/-- The conclusion of the Feit–Thompson theorem in universe `u`:
every finite group of odd order is solvable. -/
