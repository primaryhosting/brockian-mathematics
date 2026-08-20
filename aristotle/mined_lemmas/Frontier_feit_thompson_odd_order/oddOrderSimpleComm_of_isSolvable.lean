/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)
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

/-- Every divisor of an odd natural number is odd. -/

theorem oddOrderSimpleComm_of_isSolvable
    (h : ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G) :
    OddOrderSimpleComm.{u} := by
  intro S _ _ hodd hsimp
  exact IsSimpleGroup.comm_iff_isSolvable.mpr (h S hodd)

/-- The Feit–Thompson theorem is *equivalent* to its simple-group form. -/
