import Mathlib
namespace Brockian.EvenPerfectLastDigit
/-- Every even perfect number ends in 6 or 8 (its last decimal digit is 6 or 8).
    Replace the sorry with a complete proof; axiom-clean, no sorry. -/
theorem even_perfect_last_digit {n : ℕ} (he : Even n) (hp : Nat.Perfect n) :
    n % 10 = 6 ∨ n % 10 = 8 := by
  sorry
end Brockian.EvenPerfectLastDigit
