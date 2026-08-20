import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankeny_p_dvd_yz_of_zmod_zero
    {n p : ℕ} {x y z : ℤ}
    (hp : Nat.Prime p) (hp4 : p % 4 = 3)
    (hp_not_dvd_n : ¬ p ∣ n)
    (hn_mod : (n : ZMod p) = (x : ZMod p) ^ 2)
    (hZ0 : ((y ^ 2 + (n : ℤ) * z ^ 2 : ℤ) : ZMod p) = 0) :
    (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  -- Turn `y^2 + n*z^2 = 0` into `y^2 = -(x*z)^2`.
  have hy2_eq : (y : ZMod p) ^ 2 = -((x : ZMod p) * (z : ZMod p)) ^ 2 := by
    have h0 : (y : ZMod p) ^ 2 + (n : ZMod p) * (z : ZMod p) ^ 2 = 0 := by
      simpa [pow_two, Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, add_comm,
        add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hZ0
    have hy : (y : ZMod p) ^ 2 = -((n : ZMod p) * (z : ZMod p) ^ 2) :=
      eq_neg_of_add_eq_zero_left h0
    have hy' : (y : ZMod p) ^ 2 = -(((x : ZMod p) ^ 2) * (z : ZMod p) ^ 2) := by
      simpa [hn_mod] using hy
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy'

  have hxz0 : (x : ZMod p) * (z : ZMod p) = 0 := by
    by_contra hxz_ne
    have : p % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p)
        (x := (y : ZMod p)) (y := (x : ZMod p) * (z : ZMod p))
        hxz_ne (by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2_eq)
    exact this (by simpa [hp4])

  have hx0 : (x : ZMod p) ≠ 0 := by
    intro hx
    have : (n : ZMod p) = 0 := by simpa [hn_mod, hx]
    exact hp_not_dvd_n ((ZMod.natCast_eq_zero_iff n p).1 this)

  have hz0 : (z : ZMod p) = 0 := by
    exact mul_eq_zero.mp hxz0 |>.resolve_left hx0

  have hy0 : (y : ZMod p) = 0 := by
    have : (y : ZMod p) ^ 2 = 0 := by simpa [hxz0] using hy2_eq
    have : (y : ZMod p) * (y : ZMod p) = 0 := by simpa [pow_two] using this
    exact (mul_eq_zero.mp this).elim id id

  have hp_dvd_y : (p : ℤ) ∣ y :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0)
  have hp_dvd_z : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 (by simpa using hz0)
  exact ⟨hp_dvd_y, hp_dvd_z⟩

/-!
### Q₁ variant of the mod-`p` divisibility kernel

For the `Q₁ = qx² + y² + nz²` route we get an identity
\[
  y^2 + n z^2 = q K
\]
instead of `2*q*K`. The core ZMod(`p`) argument is identical: if `p ∣ K` then the RHS
vanishes mod `p`, so we again obtain `y^2 = -(x*z)^2` in `ZMod p` and force `p ∣ y,z`
when `p % 4 = 3`.

This lemma is intentionally “small” (no valuation recursion): it should be reusable
inside the eventual Q₁ descent proof.
-/
