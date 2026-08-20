import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma volume_ankenyEllipsoidL2_q1_gt_nat (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    (8 * n * q : ℝ≥0∞) < volume (ankenyEllipsoidL2_q1 (n : ℝ) (q : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hvol := volume_ankenyEllipsoidL2_q1_eq (n := (n : ℝ)) (q := (q : ℝ)) hnR hqR
  have hpi : (1 : ℝ) < Real.pi / 3 := one_lt_pi_div_three
  have ha : 0 < (8 * ((n : ℝ) * (q : ℝ)) : ℝ) := by nlinarith
  have hmul : (8 * ((n : ℝ) * (q : ℝ)) : ℝ) < (8 * ((n : ℝ) * (q : ℝ))) * (Real.pi / 3) := by
    simpa [mul_assoc] using (mul_lt_mul_of_pos_left hpi ha)
  have hpos : 0 < (8 * ((n : ℝ) * (q : ℝ))) * (Real.pi / 3 : ℝ) := by
    have : 0 < (Real.pi / 3 : ℝ) := lt_trans (by norm_num) hpi
    exact mul_pos ha this
  have hof :
      ENNReal.ofReal (8 * ((n : ℝ) * (q : ℝ)) : ℝ) <
        ENNReal.ofReal ((8 * ((n : ℝ) * (q : ℝ))) * (Real.pi / 3 : ℝ)) := by
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 hmul
  -- rewrite LHS as nat-cast `8*n*q` and RHS as `volume ...`
  have : (8 * n * q : ℝ≥0∞) < volume (ankenyEllipsoidL2_q1 (n : ℝ) (q : ℝ)) := by
    -- `simp` bridges nat casts and `ofReal`.
    simpa [hvol, mul_assoc, mul_left_comm, mul_comm] using hof
  simpa using this

/-- Generalized “Dirichlet prime in a CRT class” lemma used by Ankeny:

Given `Odd n` and a coefficient `r` that is a unit in `ZMod n`, there exists a prime `q`
such that `q % 4 = 1` and
\[
  q \equiv -(r)^{-1} \pmod n.
\]

This is the right abstraction boundary: the Jacobi-symbol computation only needs the
congruence `r*q ≡ -1 (mod n)`, which follows from `q = -(r)⁻¹` in `ZMod n`. -/
