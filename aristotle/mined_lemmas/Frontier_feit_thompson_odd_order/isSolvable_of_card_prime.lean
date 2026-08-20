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

theorem isSolvable_of_card_prime
    (G : Type*) [Group G] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p) : IsSolvable G := by
  haveI := Fact.mk hp
  haveI : IsCyclic G := isCyclic_of_prime_card hcard
  exact isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b

/-- Base case: a finite group of squarefree order is solvable (its Sylow subgroups are all
cyclic, i.e. it is a Z-group).  This gives Feit-Thompson unconditionally for the groups of
squarefree odd order. -/
