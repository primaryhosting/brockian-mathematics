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

lemma integrableOn_id_mul_fermi_affine {c : ℝ} (hc : 0 < c) (d r : ℝ) :
    IntegrableOn (fun x => x * fermi (c * x + d)) (Ioi r) := by
  refine integrable_of_isBigO_exp_neg (b := c/2) (by positivity)
    ((continuous_id.mul (continuous_fermi.comp (by fun_prop))).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound (Real.exp (-d) / c) ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ),
    Filter.eventually_ge_atTop (-d/c)] with x hx hxd
  have hnn : 0 ≤ x * fermi (c * x + d) := mul_nonneg hx (fermi_pos _).le
  have h1 : fermi (c * x + d) ≤ Real.exp (-(c * x + d)) := fermi_le_exp_neg _
  have h2 : c * x ≤ Real.exp (c * x / 2) := le_exp_half (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_pos (Real.exp_pos _)]
  have hx' : x ≤ Real.exp (c * x / 2) / c := by
    rw [le_div_iff₀ hc]; linarith [h2]
  calc x * fermi (c * x + d)
      ≤ (Real.exp (c * x / 2) / c) * Real.exp (-(c * x + d)) := by
        apply mul_le_mul hx' h1 (fermi_pos _).le (by positivity)
    _ = (Real.exp (-d) / c) * Real.exp (-(c/2) * x) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
        ring_nf

/-! ## The basic Fermi–Dirac integral `∫₀^∞ v / (1 + e^v) dv = π² / 12` -/

/-- `∑ 1 / (n + 1) ^ 2 = π ^ 2 / 6`, the Basel problem in shifted indexing. -/
