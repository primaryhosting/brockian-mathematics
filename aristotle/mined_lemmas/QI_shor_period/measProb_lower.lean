/-
The quantum period-finding subroutine: the state produced by the algorithm,
the measurement distribution of the first register, and the lower bound on the
probability of a "good" measurement outcome.
-/
import Mathlib
import RequestProject.Analysis

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 2000000

namespace QI

/-- The primitive `Q`-th root of unity `e^{2πi/Q}` used by the quantum Fourier transform. -/

theorem measProb_lower (m : ℕ) (hr : 0 < r) (h4 : 4 * r ≤ Q)
    (hf : ∀ j k : ℕ, f j = f k ↔ j % r = k % r)
    (s d : ℤ) (hd : ((r * m : ℕ) : ℤ) = s * Q + d) (hds : 2 * |d| ≤ r) :
    1 / (16 * (r : ℝ)) ≤ measProb Q f m := by
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  norm_num at hpi2
  have hQ0 : 0 < Q := by omega
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h5 : (4 : ℝ) * r ≤ Q := by exact_mod_cast h4
  set t : ℝ := (d : ℝ) / Q with ht
  have hzt : omega Q ^ (r * m) = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) :=
    omega_pow_int Q (r * m) s d hd hQ0
  have hdR : |(d : ℝ)| ≤ (r : ℝ) / 2 := by
    have : (2 : ℝ) * |(d : ℝ)| ≤ r := by exact_mod_cast hds
    linarith
  have htabs : |t| ≤ (r : ℝ) / (2 * Q) := by
    rw [ht, abs_div, abs_of_pos hQR, div_le_div_iff₀ hQR (by positivity)]
    nlinarith
  set A0 : ℕ := Q / r with hA0
  have hA0ge : (Q : ℝ) - r ≤ r * A0 := by
    have h3 : Q - r ≤ r * (Q / r) := by
      have h := Nat.div_add_mod Q r
      have h2 : Q % r < r := Nat.mod_lt _ hr
      omega
    have h3' : Q - r ≤ r * A0 := by rw [hA0]; exact h3
    have h4' := (Nat.cast_le (α := ℝ)).mpr h3'
    push_cast at h4'
    rw [Nat.cast_sub (by omega : r ≤ Q)] at h4'
    linarith
  have hkey : ∀ k ∈ Finset.range r, ((6 / (5 * Real.pi)) * A0) ^ 2 ≤
      ‖∑ l ∈ Finset.range (blockCount Q r k), (omega Q ^ (r * m)) ^ l‖ ^ 2 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hA0le : A0 ≤ blockCount Q r k := by
      rw [blockCount, hA0]; exact Nat.div_le_div_right (by omega)
    have hblockle : (blockCount Q r k : ℝ) ≤ ((Q : ℝ) + r) / r := by
      rw [blockCount, le_div_iff₀ (by positivity)]
      have h1 : (Q - k + r - 1) / r * r ≤ Q - k + r - 1 := Nat.div_mul_le_self _ _
      have h2 : ((Q - k + r - 1) / r * r : ℕ) ≤ ((Q + r : ℕ) : ℝ) := by
        exact_mod_cast le_trans h1 (by omega)
      push_cast at h2 ⊢
      linarith
    have hbound : |(blockCount Q r k : ℝ) * t| ≤ 5 / 8 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (blockCount Q r k : ℝ))]
      have hmul : (blockCount Q r k : ℝ) * |t| ≤ (((Q : ℝ) + r) / r) * ((r : ℝ) / (2 * Q)) :=
        mul_le_mul hblockle htabs (abs_nonneg t) (by positivity)
      have heq : (((Q : ℝ) + r) / r) * ((r : ℝ) / (2 * Q)) = ((Q : ℝ) + r) / (2 * Q) := by
        field_simp
      rw [heq] at hmul
      have hlast : ((Q : ℝ) + r) / (2 * Q) ≤ 5 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
        linarith
      linarith
    rw [hzt]
    have hg := geom_norm_lower (blockCount Q r k) t hbound
    have hmono : (6 / (5 * Real.pi)) * A0 ≤ (6 / (5 * Real.pi)) * (blockCount Q r k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast hA0le
    exact pow_le_pow_left₀ (by positivity) (le_trans hmono hg) 2
  rw [measProb_eq f Q r m hr (by omega) hf]
  have hsum : (r : ℝ) * ((6 / (5 * Real.pi)) * A0) ^ 2 ≤
      ∑ k ∈ Finset.range r, ‖∑ l ∈ Finset.range (blockCount Q r k), (omega Q ^ (r * m)) ^ l‖ ^ 2 := by
    calc (r : ℝ) * ((6 / (5 * Real.pi)) * A0) ^ 2
        = ∑ _k ∈ Finset.range r, ((6 / (5 * Real.pi)) * A0) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range]; simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hkey
  have hfinal : 1 / (16 * (r : ℝ)) ≤
      ((Q : ℝ)⁻¹) ^ 2 * ((r : ℝ) * ((6 / (5 * Real.pi)) * A0) ^ 2) := by
    have hA0pos : (0 : ℝ) ≤ A0 := by positivity
    have hkey2 : (3 : ℝ) / 4 * Q ≤ r * A0 := by linarith
    rw [div_le_iff₀ (by positivity)]
    have hexp : ((Q : ℝ)⁻¹) ^ 2 * ((r : ℝ) * ((6 / (5 * Real.pi)) * A0) ^ 2) * (16 * r)
        = (16 * 36 / (25 * Real.pi ^ 2)) * (((r : ℝ) * A0) ^ 2 / Q ^ 2) := by
      field_simp; ring
    rw [hexp]
    have h1 : (9 : ℝ) / 16 ≤ ((r : ℝ) * A0) ^ 2 / Q ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hp2 : Real.pi ^ 2 < 12.96 := by nlinarith
    have h2 : (1 : ℝ) ≤ (16 * 36 / (25 * Real.pi ^ 2)) * (9 / 16) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hc : (0 : ℝ) < 16 * 36 / (25 * Real.pi ^ 2) := by positivity
    calc (1 : ℝ) ≤ (16 * 36 / (25 * Real.pi ^ 2)) * (9 / 16) := h2
      _ ≤ (16 * 36 / (25 * Real.pi ^ 2)) * (((r : ℝ) * A0) ^ 2 / Q ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hc.le
  have hmul2 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ ((Q : ℝ)⁻¹) ^ 2)
  linarith

end Periodic

end QI

/-
Analytic ingredients for the Shor period-finding proof:
norms of geometric sums of roots of unity and the Jordan-type sine bound.
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace QI

/-- `‖e^{ix} - 1‖ = 2|sin (x/2)|`. -/
