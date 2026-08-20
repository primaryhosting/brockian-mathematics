import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


universe u'

namespace Frontier

/-- The Feit–Thompson odd order theorem, as a proposition: every finite group of odd order
is solvable. -/

theorem feit_thompson_odd_order
    (hsimple : ∀ (S : Type u') [Group S] [Finite S],
      IsSimpleGroup S → Odd (Nat.card S) → IsSolvable S)
    (G : Type u') [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G :=
  solvable_of_odd_aux hsimple (Nat.card G) G le_rfl hG

/-- The reduction, stated with the two `Prop`-valued abbreviations. -/
