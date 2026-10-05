import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Unconditional base cases -/

/-- A finite group whose order is squarefree is solvable (it is a Z-group). -/

def SimpleOddAbelian : Prop :=
  ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S → Odd (Nat.card S) →
    ∀ a b : S, a * b = b * a

/-- The odd order theorem is *equivalent* to the assertion that every finite simple group of
odd order is abelian.  The forward implication is `Frontier.feit_thompson_odd_order`; the
backward implication holds because a simple solvable group is abelian. -/
