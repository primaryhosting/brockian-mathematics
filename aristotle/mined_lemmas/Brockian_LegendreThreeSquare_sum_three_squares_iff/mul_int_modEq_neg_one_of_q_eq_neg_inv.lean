import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma mul_int_modEq_neg_one_of_q_eq_neg_inv
    (n r q : ℕ) (hr : IsUnit (r : ZMod n)) (hq_mod : (q : ZMod n) = - (r : ZMod n)⁻¹) :
    ((r : ℤ) * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] := by
  have hZ : (r : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
    calc
      (r : ZMod n) * (q : ZMod n)
          = (r : ZMod n) * (-(r : ZMod n)⁻¹) := by simp [hq_mod]
      _ = -((r : ZMod n) * (r : ZMod n)⁻¹) := by simp [mul_neg]
      _ = (-1 : ZMod n) := by simp [ZMod.mul_inv_of_unit (r : ZMod n) hr]
  have hZ_int : ((r : ℤ) : ZMod n) * ((q : ℤ) : ZMod n) = (-1 : ZMod n) := by
    simpa using hZ
  have hZ_cast : (((r : ℤ) * (q : ℤ)) : ℤ) ≡ (-1 : ℤ) [ZMOD n] := by
    exact (ZMod.intCast_eq_intCast_iff ((r : ℤ) * (q : ℤ)) (-1 : ℤ) n).1 (by
      simpa [Int.cast_mul] using hZ_int)
  -- normalize multiplication order on ℤ
  simpa [mul_assoc, mul_comm, mul_left_comm] using hZ_cast

/-- A tiny `Int.ModEq` “restriction of modulus” helper:

If \(a \equiv b \pmod M\) and \(m \mid M\), then \(a \equiv b \pmod m\).

This is used to avoid repeating `dvd_trans` / `modEq_iff_dvd` boilerplate when we
intentionally prove a congruence modulo a larger number than we need. -/
