import Mathlib
namespace Brockian.OddPerfectMod4
/-- An odd perfect number is congruent to 1 modulo 4. Prove; axiom-clean, no sorry. -/
theorem oddPerfect_mod4 {n : ℕ} (ho : Odd n) (hp : Nat.Perfect n) : n % 4 = 1 := by
  sorry
end Brockian.OddPerfectMod4
