/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
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

set_option grind.warning false

namespace Frontier

open MeasureTheory Set Real

/-! ## Mirzakhani's integration kernel

Mirzakhani's recursion for Weil–Petersson volumes of moduli spaces of bordered
hyperbolic surfaces is driven by the kernel

`H (x, t) = 1 / (1 + exp ((x + t) / 2)) + 1 / (1 + exp ((x - t) / 2))`.

We write `wpPhi u = 1 / (1 + exp (u / 2))`, so that `H (x, t) = wpPhi (x+t) + wpPhi (x-t)`.
-/

/-- The basic Fermi–Dirac type profile `u ↦ 1 / (1 + e^{u/2})` out of which Mirzakhani's
integration kernel is built. -/

theorem int_id_mul_wpPhi : (∫ u in Ioi (0:ℝ), u * wpPhi u) = Real.pi ^ 2 / 3 := by
  set F : ℕ → ℝ → ℝ := fun n u => (-1:ℝ) ^ n * (u * Real.exp (-(((n:ℝ) + 1) / 2 * u))) with hF
  have hpos : ∀ n : ℕ, (0:ℝ) < ((n:ℝ) + 1) / 2 := by intro n; positivity
  have hint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    (intOn_id_exp _ (hpos n)).const_mul ((-1:ℝ) ^ n)
  have hnorm : ∀ n : ℕ, ∫ u in Ioi (0:ℝ), ‖F n u‖ = 4 / ((n:ℝ) + 1) ^ 2 := by
    intro n
    have e : ∫ u in Ioi (0:ℝ), ‖F n u‖
        = ∫ u in Ioi (0:ℝ), u * Real.exp (-(((n:ℝ) + 1) / 2 * u)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [mem_Ioi] at hx
      rw [hF]
      simp only []
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul,
        Real.norm_eq_abs, abs_of_pos hx, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [e, int_id_exp _ (hpos n)]
    field_simp
    ring
  have hsum : Summable (fun n : ℕ => ∫ u in Ioi (0:ℝ), ‖F n u‖) := by
    have hs : Summable (fun n : ℕ => 4 / ((n:ℝ) + 1) ^ 2) := by
      have h1 := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      have h2 := ((summable_nat_add_iff 1).2 h1).mul_left 4
      apply h2.congr
      intro n
      push_cast
      ring
    exact hs.congr (fun n => (hnorm n).symm)
  have key := integral_tsum_of_summable_integral_norm (F := F) hint hsum
  have hL : ∑' (n : ℕ), ∫ u in Ioi (0:ℝ), F n u = Real.pi ^ 2 / 3 := by
    have e : ∀ n : ℕ, (∫ u in Ioi (0:ℝ), F n u) = 4 * ((-1:ℝ) ^ n / ((n:ℝ) + 1) ^ 2) := by
      intro n
      rw [hF]
      simp only []
      rw [integral_const_mul, int_id_exp _ (hpos n)]
      field_simp
      ring
    rw [tsum_congr e, (altBasel.mul_left 4).tsum_eq]
    ring
  have hR : (∫ u in Ioi (0:ℝ), ∑' (n : ℕ), F n u) = ∫ u in Ioi (0:ℝ), u * wpPhi u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp only [mem_Ioi] at hu
    show ∑' (n : ℕ), F n u = u * wpPhi u
    rw [wpPhi_series u hu, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [hF]
    ring
  rw [← hR, ← key, hL]

/-! ## Mirzakhani's kernel integral `F₁` -/

