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

theorem odd_of_dvd_odd {m n : ℕ} (hmn : m ∣ n) (hn : Odd n) : Odd m :=
  hn.of_dvd_nat hmn

/-- If `G` is a nontrivial group that is not simple, then it has a normal subgroup that is
neither trivial nor everything. -/
