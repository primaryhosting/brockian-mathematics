import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma mod8_eq_six_of_reduced (t : ℕ)
    (ht4 : ¬ 4 ∣ t) (ht7 : t % 8 ≠ 7) (ht3 : t % 8 ≠ 3)
    (ht1 : t % 8 ≠ 1) (ht2 : t % 8 ≠ 2) (ht5 : t % 8 ≠ 5) :
    t % 8 = 6 := by
  have : t % 8 = 0 ∨ t % 8 = 1 ∨ t % 8 = 2 ∨ t % 8 = 3 ∨ t % 8 = 4 ∨ t % 8 = 5 ∨ t % 8 = 6 ∨ t % 8 = 7 := by
    omega
  rcases this with h0 | h1 | h2' | h3 | h4 | h5' | h6 | h7
  · exfalso
    exact ht4 (four_dvd_of_mod8_eq0 t h0)
  · exact False.elim (ht1 h1)
  · exact False.elim (ht2 h2')
  · exact False.elim (ht3 h3)
  · exfalso
    exact ht4 (four_dvd_of_mod8_eq4 t h4)
  · exact False.elim (ht5 h5')
  · exact h6
  · exact False.elim (ht7 h7)

/-!
### Squarefree `5 mod 8` branch (Q₁ route)

Ankeny reduces to the squarefree case up front. We do the same: prove the squarefree case via Q₁,
then lift by scaling (`s^2 * m`) using `sum_three_squares_mul_sq`.
-/
