import Mathlib
namespace Brockian.EvenPerfectMod9
/-- Every even perfect number greater than 6 is congruent to 1 modulo 9. Prove; axiom-clean, no sorry. -/
theorem even_perfect_mod9 {n : ℕ} (he : Even n) (hp : Nat.Perfect n) (h6 : 6 < n) : n % 9 = 1 := by
  sorry
end Brockian.EvenPerfectMod9
