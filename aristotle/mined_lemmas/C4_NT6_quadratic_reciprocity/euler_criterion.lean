import Mathlib
namespace C4.NT6

/-- Quadratic reciprocity for distinct odd primes: this is
`legendreSym.quadratic_reciprocity` up to commutativity of multiplication. -/

theorem euler_criterion (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) (ha : a ≠ 0) :
    IsSquare a ↔ a ^ ((p-1)/2) = 1 := by
  have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
  obtain ⟨k, hk⟩ := hodd
  have h1 : (p - 1) / 2 = p / 2 := by omega
  rw [h1]
  exact ZMod.euler_criterion p ha

/-- There are infinitely many primes. -/
