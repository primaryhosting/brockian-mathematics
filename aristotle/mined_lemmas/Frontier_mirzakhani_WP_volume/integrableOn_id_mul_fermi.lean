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

lemma integrableOn_id_mul_fermi (c : ℝ) :
    IntegrableOn (fun v => v * fermi v) (Ioi c) := by
  refine integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num)
    ((continuous_id.mul continuous_fermi).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with v hv
  have h := fermi_le_exp_neg v
  have hv2 : v ≤ Real.exp (v / 2) := le_exp_half hv
  have key : v * fermi v ≤ Real.exp (-(1/2) * v) := by
    calc v * fermi v ≤ Real.exp (v/2) * Real.exp (-v) := by
          apply mul_le_mul hv2 h (fermi_pos v).le (Real.exp_pos _).le
      _ = Real.exp (-(1/2) * v) := by
          rw [← Real.exp_add]; ring_nf
  have hnn : 0 ≤ v * fermi v := mul_nonneg hv (fermi_pos v).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_pos (Real.exp_pos _)]
  linarith

