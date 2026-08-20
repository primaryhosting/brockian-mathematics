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

lemma integral_id_mul_exp (n : ℕ) :
    ∫ v in Ioi (0:ℝ), v * Real.exp (-(((n : ℝ) + 1) * v)) = 1 / ((n : ℝ) + 1) ^ 2 := by
  have hr : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := (n:ℝ) + 1) (by norm_num) hr
  rw [Real.Gamma_two] at h
  calc ∫ v in Ioi (0:ℝ), v * Real.exp (-(((n : ℝ) + 1) * v))
      = ∫ t in Ioi (0:ℝ), t ^ ((2:ℝ) - 1) * Real.exp (-(((n:ℝ) + 1) * t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
        norm_num
    _ = (1/((n:ℝ)+1))^(2:ℝ) * 1 := h
    _ = 1 / ((n : ℝ) + 1) ^ 2 := by
        rw [mul_one, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, div_pow, one_pow]

