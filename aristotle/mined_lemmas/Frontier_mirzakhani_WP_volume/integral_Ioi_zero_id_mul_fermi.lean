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

/-!
## Overview

Mathlib contains no theory of moduli spaces of bordered Riemann surfaces or of
Weil–Petersson volumes, so the objects entering Mirzakhani's recursion are defined here from
scratch.  The two nontrivial inputs taken from Mathlib are the Basel sum `hasSum_zeta_two`
(`∑ 1 / n ^ 2 = π ^ 2 / 6`) and the Gamma-integral evaluation
`Real.integral_rpow_mul_exp_neg_mul_Ioi`; everything else (the Fermi–Dirac integral
`∫₀^∞ v / (1 + e ^ v) dv = π ^ 2 / 12`, the first moment of Mirzakhani's kernel, and the
recursion itself) is proved below.
-/

namespace Frontier

open MeasureTheory Set

/-! ## The Fermi–Dirac weight and Mirzakhani's kernel -/

/-- The Fermi–Dirac weight `σ (y) = 1 / (1 + e ^ y)` occurring in Mirzakhani's kernel. -/

lemma integral_Ioi_zero_id_mul_fermi :
    ∫ v in Ioi (0:ℝ), v * fermi v = Real.pi ^ 2 / 12 := by
  set F : ℕ → ℝ → ℝ := fun n v => (-1 : ℝ) ^ n * (v * Real.exp (-(((n : ℝ) + 1) * v)))
    with hF
  have hint : ∀ n, IntegrableOn (F n) (Ioi (0:ℝ)) := fun n =>
    (integrableOn_id_mul_exp n).const_mul _
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Ioi (0:ℝ))) :=
    fun n => (hint n).aestronglyMeasurable
  have hnormint : ∀ n, ∫ v in Ioi (0:ℝ), ‖F n v‖ = 1 / ((n:ℝ)+1)^2 := by
    intro n
    rw [← integral_id_mul_exp n]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    have hv' : (0:ℝ) < v := hv
    rw [hF]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg hv'.le, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hfin : ∑' n : ℕ, ∫⁻ v in Ioi (0:ℝ), ‖F n v‖ₑ ≠ ⊤ := by
    have hcast : ∀ n : ℕ, ∫⁻ v in Ioi (0:ℝ), ‖F n v‖ₑ = ENNReal.ofReal (1 / ((n:ℝ)+1)^2) := by
      intro n
      rw [← hnormint n, ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    rw [tsum_congr hcast, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      hasSum_shift.summable]
    exact ENNReal.ofReal_ne_top
  have hts := integral_tsum hmeas hfin
  have hlhs : ∫ v in Ioi (0:ℝ), ∑' n : ℕ, F n v = ∫ v in Ioi (0:ℝ), v * fermi v :=
    setIntegral_congr_fun measurableSet_Ioi (fun v hv => (hasSum_fermi_series hv).tsum_eq)
  have hrhs : ∑' n : ℕ, ∫ v in Ioi (0:ℝ), F n v = Real.pi ^ 2 / 12 := by
    have hterm : ∀ n : ℕ, ∫ v in Ioi (0:ℝ), F n v = (-1:ℝ)^n / ((n:ℝ)+1)^2 := by
      intro n
      rw [hF]
      simp only
      rw [integral_const_mul, integral_id_mul_exp n]
      ring
    rw [tsum_congr hterm]
    exact hasSum_alt_zeta_two.tsum_eq
  rw [← hlhs, hts, hrhs]

/-! ## Symmetric interval integrals -/

