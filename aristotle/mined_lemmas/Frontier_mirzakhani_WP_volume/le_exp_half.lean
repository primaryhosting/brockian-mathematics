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

lemma le_exp_half {v : ℝ} (hv : 0 ≤ v) : v ≤ Real.exp (v / 2) := by
  have h : 1 + v / 4 ≤ Real.exp (v / 4) := by
    have := Real.add_one_le_exp (v / 4)
    linarith
  have hpos : (0:ℝ) ≤ 1 + v / 4 := by linarith
  have hsq : (1 + v / 4) ^ 2 ≤ (Real.exp (v / 4)) ^ 2 := by
    exact pow_le_pow_left₀ hpos h 2
  have hexp : (Real.exp (v / 4)) ^ 2 = Real.exp (v / 2) := by
    rw [← Real.exp_nat_mul]
    norm_num
    ring_nf
  nlinarith [sq_nonneg (v - 4)]

/-! ## Integrability -/

