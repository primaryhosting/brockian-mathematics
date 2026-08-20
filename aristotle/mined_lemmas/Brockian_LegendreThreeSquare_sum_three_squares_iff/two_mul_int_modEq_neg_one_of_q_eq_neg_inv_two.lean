import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma two_mul_int_modEq_neg_one_of_q_eq_neg_inv_two
    (n q : ℕ) (hn : Odd n) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    (2 * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] := by
  have h2unit : IsUnit (2 : ZMod n) := zmod_isUnit_two_of_odd n hn
  have hZ : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
    calc
      (2 : ZMod n) * (q : ZMod n)
          = (2 : ZMod n) * (-(2 : ZMod n)⁻¹) := by simp [hq_mod]
      _ = -((2 : ZMod n) * (2 : ZMod n)⁻¹) := by simp [mul_neg]
      _ = (-1 : ZMod n) := by simp [ZMod.mul_inv_of_unit (2 : ZMod n) h2unit]
  have hZ_int : ((2 : ℤ) : ZMod n) * ((q : ℤ) : ZMod n) = (-1 : ZMod n) := by
    simpa using hZ
  have hZ_cast : ((2 : ℤ) * (q : ℤ) : ℤ) ≡ (-1 : ℤ) [ZMOD n] := by
    exact (ZMod.intCast_eq_intCast_iff ((2 : ℤ) * (q : ℤ)) (-1 : ℤ) n).1 (by
      simpa [Int.cast_mul] using hZ_int)
  simpa [mul_assoc, mul_comm, mul_left_comm] using hZ_cast

/-- General cast bridge used in the Ankeny pipeline:

If `q = -(r)⁻¹` in `ZMod n` (with `r` a unit in `ZMod n`), then
\[
  rq \equiv -1 \pmod n.
\]

We keep the hypotheses minimal: it’s enough that `r` is a unit in `ZMod n`.
(For our main uses: `r = 1` always, and `r = 2` when `n` is odd.) -/
