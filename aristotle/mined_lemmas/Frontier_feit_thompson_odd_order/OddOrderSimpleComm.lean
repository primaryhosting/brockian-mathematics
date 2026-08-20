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

def OddOrderSimpleComm : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    Odd (Nat.card S) → IsSimpleGroup S → ∀ a b : S, a * b = b * a

/-- Auxiliary induction: assuming that all finite simple groups of odd order are
commutative, every finite group of odd order and cardinality `n` is solvable. -/
