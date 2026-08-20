import Mathlib

namespace Brockian.EvenPerfectLastDigit

/-- The core of the Euclid--Euler argument.  If the exact power of two in a
perfect number is `2^k`, its odd part is the corresponding Mersenne prime. -/

theorem even_perfect_last_digit {n : ℕ} (he : Even n) (hp : Nat.Perfect n) :
    n % 10 = 6 ∨ n % 10 = 8 := by
  obtain ⟨p, hprime, rfl⟩ := even_perfect_classification he hp
  exact euclidEuler_form_last_digit hprime

end Brockian.EvenPerfectLastDigit

