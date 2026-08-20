import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma four_dvd_of_mod8_eq4 (t : ℕ) (ht4 : t % 8 = 4) : 4 ∣ t := by
  -- `t = (t % 8) + 8*(t/8) = 4 + 8*(t/8) = 4*(1 + 2*(t/8))`.
  refine ⟨1 + 2 * (t / 8), ?_⟩
  have ht_eq : t = t % 8 + 8 * (t / 8) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mod_add_div t 8).symm
  calc
    t = 4 + 8 * (t / 8) := by simpa [ht4] using ht_eq
    _ = 4 * (1 + 2 * (t / 8)) := by ring

