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

theorem feit_thompson_odd_order_iff :
    OddOrderSimpleComm.{u} ↔
      ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G :=
  ⟨fun h G _ _ hodd => feit_thompson_odd_order h G hodd, oddOrderSimpleComm_of_isSolvable⟩

/-- Base case (unconditional): a finite group of prime power order is solvable. -/
