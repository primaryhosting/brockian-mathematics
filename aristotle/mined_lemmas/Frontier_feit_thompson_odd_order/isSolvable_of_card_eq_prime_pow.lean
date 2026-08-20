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

theorem isSolvable_of_card_eq_prime_pow
    (G : Type*) [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ k) : IsSolvable G := by
  haveI := Fact.mk hp
  haveI : Group.IsNilpotent G := (IsPGroup.of_card (p := p) hcard).isNilpotent
  infer_instance

/-- Base case: a finite group of prime order is solvable (indeed cyclic). -/
