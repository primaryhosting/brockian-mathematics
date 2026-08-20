import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma sum_three_squares_of_five_mod_eight (t : ℕ) (ht : t % 8 = 5) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = t := by
  obtain ⟨s, m, hm_eq, hm_sq⟩ := exists_squarefree_part t
  have hm5 : m % 8 = 5 := squarefree_part_mod_eight_five t s m hm_eq ht
  obtain ⟨x, y, z, hm_rep⟩ := sum_three_squares_of_five_mod_eight_squarefree m hm5 hm_sq
  have hs_rep : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = s ^ 2 * m :=
    sum_three_squares_mul_sq s m ⟨x, y, z, hm_rep⟩
  rcases hs_rep with ⟨x', y', z', ht_rep⟩
  refine ⟨x', y', z', ?_⟩
  simpa [hm_eq] using ht_rep

