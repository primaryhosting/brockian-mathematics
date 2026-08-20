import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma exists_b_sq_congr_neg_mod_q_of_jacobi
    (n q : ℕ) (hq : Nat.Prime q) (hJ : J(-(n : ℤ) | q) = 1) :
    ∃ b : ℤ, b ^ 2 ≡ - (n : ℤ) [ZMOD (q : ℤ)] := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hsq_q : IsSquare (-(n : ZMod q)) := by
    simpa [Int.cast_neg, Int.cast_natCast] using
      (ZMod.isSquare_of_jacobiSym_eq_one (p := q) (a := (-(n : ℤ))) hJ)
  rcases hsq_q with ⟨r, hr⟩
  rcases ZMod.intCast_surjective r with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  have hr' : ((b : ZMod q) ^ 2) = (-(n : ℤ) : ZMod q) := by
    -- `IsSquare` for `ZMod q` yields `-(n) = r*r`; rewrite into a `^2` statement.
    have : (r ^ 2) = (-(n : ZMod q)) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hr.symm
    simpa [hb, Int.cast_neg, Int.cast_natCast] using this
  exact (ZMod.intCast_eq_intCast_iff (b ^ 2) (-(n : ℤ)) q).1 (by
    simpa [Int.cast_pow, pow_two] using hr')

