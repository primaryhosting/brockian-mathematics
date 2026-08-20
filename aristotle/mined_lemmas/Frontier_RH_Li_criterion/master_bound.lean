/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Complex Filter

/-!
## Elementary complex-analytic estimates
-/

/-- Geometric bound: `|1 - r ^ n| ≤ n |1 - r| max(1,r) ^ n` for real `r ≥ 0`. -/

theorem master_bound (z : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    |1 - (z ^ n).re| ≤
      2 * (n : ℝ) ^ 2 * (1 + max 0 (‖z‖ - 1)) ^ n * ((1 - z.re) + 2 * max 0 (‖z‖ - 1)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · have hz0 : ((0 : ℂ) ^ n).re = 0 := by rw [zero_pow (by omega)]; simp
    rw [hz0]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simp only [norm_zero, Complex.zero_re, sub_zero, zero_sub]
    have hmx : max (0 : ℝ) (-1) = 0 := by norm_num
    rw [hmx]
    simp only [add_zero, one_pow, mul_one, mul_zero]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith
  set r : ℝ := ‖z‖ with hrdef
  have hr0 : 0 < r := norm_pos_iff.mpr hz
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  set w : ℂ := z / (r : ℂ) with hwdef
  have hw1 : ‖w‖ = 1 := by
    rw [hwdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, ← hrdef,
      div_self hr0.ne']
  have hzw : z = (r : ℂ) * w := by rw [hwdef]; field_simp
  have hzre : z.re = r * w.re := by rw [hzw]; simp
  have hzpow : (z ^ n).re = r ^ n * (w ^ n).re := by
    rw [hzw, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  set e : ℝ := max 0 (r - 1) with hedef
  set d : ℝ := 1 - z.re with hddef
  set u : ℝ := 1 - w.re with hudef
  have he0 : 0 ≤ e := le_max_left _ _
  have hu0 : 0 ≤ u := by
    have : w.re ≤ ‖w‖ := Complex.re_le_norm w
    rw [hw1] at this; simp only [hudef]; linarith
  have hd : d = 1 - r + r * u := by rw [hddef, hzre, hudef]; ring
  have hde : 0 ≤ d + e := by
    have h1 : r - 1 ≤ e := le_max_right _ _
    nlinarith [mul_nonneg hr0.le hu0]
  have hR : max 1 r = 1 + e := by
    rcases le_total r 1 with h | h
    · rw [max_eq_left h, hedef, max_eq_left (by linarith)]; ring
    · rw [max_eq_right h, hedef, max_eq_right (by linarith)]; ring
  have hRpos : (0 : ℝ) < 1 + e := by linarith
  have hrR : r ≤ 1 + e := hR ▸ le_max_right _ _
  have h1r : |1 - r| ≤ d + 2 * e := by
    rcases le_total r 1 with h | h
    · rw [abs_of_nonneg (by linarith)]
      nlinarith [mul_nonneg hr0.le hu0]
    · rw [abs_of_nonpos (by linarith)]
      have : e = r - 1 := by rw [hedef, max_eq_right (by linarith)]
      linarith
  have hrnu : r ^ n * u ≤ (1 + e) ^ n * (d + 2 * e) := by
    rcases le_total r 1 with h | h
    · have he : e = 0 := by rw [hedef, max_eq_left (by linarith)]
      have hrn : r ^ n ≤ r := by
        calc r ^ n ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le h hn
        _ = r := pow_one r
      have h2 : r ^ n * u ≤ r * u := mul_le_mul_of_nonneg_right hrn hu0
      rw [he]; simp only [add_zero, one_pow, one_mul, mul_zero]
      nlinarith
    · have he : e = r - 1 := by rw [hedef, max_eq_right (by linarith)]
      have hru : r * u = d + e := by rw [hd, he]; ring
      have hrn1 : r ^ n ≤ (1 + e) ^ n * r := by
        have hh : r ^ n = r ^ (n - 1) * r := by rw [← pow_succ]; congr 1; omega
        rw [hh]
        apply mul_le_mul_of_nonneg_right _ hr0.le
        calc r ^ (n - 1) ≤ (1 + e) ^ (n - 1) := pow_le_pow_left₀ hr0.le hrR _
        _ ≤ (1 + e) ^ n := pow_le_pow_right₀ (by linarith) (by omega)
      calc r ^ n * u ≤ ((1 + e) ^ n * r) * u := mul_le_mul_of_nonneg_right hrn1 hu0
      _ = (1 + e) ^ n * (r * u) := by ring
      _ = (1 + e) ^ n * (d + e) := by rw [hru]
      _ ≤ (1 + e) ^ n * (d + 2 * e) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hRpos.le _)
  have hsplit : 1 - (z ^ n).re = (1 - r ^ n) + r ^ n * (1 - (w ^ n).re) := by rw [hzpow]; ring
  have hwn0 : 0 ≤ 1 - (w ^ n).re := by
    have : (w ^ n).re ≤ ‖w ^ n‖ := Complex.re_le_norm _
    rw [norm_pow, hw1, one_pow] at this; linarith
  have hwn : 1 - (w ^ n).re ≤ (n : ℝ) ^ 2 * u := unit_re_pow_bound w hw1 n
  have hgeom := real_geom_bound r hr0.le n
  rw [hR] at hgeom
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hstep1 : |1 - (z ^ n).re| ≤ |1 - r ^ n| + r ^ n * (1 - (w ^ n).re) := by
    rw [hsplit]
    calc |1 - r ^ n + r ^ n * (1 - (w ^ n).re)| ≤ |1 - r ^ n| + |r ^ n * (1 - (w ^ n).re)| :=
          abs_add_le _ _
    _ = |1 - r ^ n| + r ^ n * (1 - (w ^ n).re) := by
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg hr0.le _) hwn0)]
  have hA : |1 - r ^ n| ≤ (n : ℝ) * ((1 + e) ^ n * (d + 2 * e)) := by
    refine hgeom.trans ?_
    have h3 := mul_le_mul_of_nonneg_left h1r (by positivity : (0 : ℝ) ≤ (n : ℝ))
    have h4 := mul_le_mul_of_nonneg_right h3 (pow_nonneg hRpos.le n)
    calc (n : ℝ) * |1 - r| * (1 + e) ^ n ≤ (n : ℝ) * (d + 2 * e) * (1 + e) ^ n := h4
    _ = (n : ℝ) * ((1 + e) ^ n * (d + 2 * e)) := by ring
  have hB : r ^ n * (1 - (w ^ n).re) ≤ (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) := by
    calc r ^ n * (1 - (w ^ n).re) ≤ r ^ n * ((n : ℝ) ^ 2 * u) :=
          mul_le_mul_of_nonneg_left hwn (pow_nonneg hr0.le _)
    _ = (n : ℝ) ^ 2 * (r ^ n * u) := by ring
    _ ≤ (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) :=
        mul_le_mul_of_nonneg_left hrnu (by positivity)
  have hpos : 0 ≤ (1 + e) ^ n * (d + 2 * e) := mul_nonneg (pow_nonneg hRpos.le _) (by linarith)
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hlast := mul_le_mul_of_nonneg_right hnn hpos
  calc |1 - (z ^ n).re| ≤ |1 - r ^ n| + r ^ n * (1 - (w ^ n).re) := hstep1
  _ ≤ (n : ℝ) * ((1 + e) ^ n * (d + 2 * e)) + (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) := by
      linarith
  _ ≤ (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) + (n : ℝ) ^ 2 * ((1 + e) ^ n * (d + 2 * e)) := by
      linarith
  _ = 2 * (n : ℝ) ^ 2 * (1 + e) ^ n * (d + 2 * e) := by ring

/-- Simultaneous recurrence (a Dirichlet-type approximation statement): finitely many unit
complex numbers can be simultaneously brought within `ε` of `1` by a common, arbitrarily
large power. -/
