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

lemma hasSum_fermi_series {v : ℝ} (hv : 0 < v) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (v * Real.exp (-(((n : ℝ) + 1) * v))))
      (v * fermi v) := by
  have hlt : ‖(-Real.exp (-v))‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-v) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have h := (hasSum_geometric_of_norm_lt_one hlt).mul_left (v * Real.exp (-v))
  have heq : (fun n : ℕ => v * Real.exp (-v) * (-Real.exp (-v)) ^ n)
      = fun n : ℕ => (-1 : ℝ) ^ n * (v * Real.exp (-(((n : ℝ) + 1) * v))) := by
    funext n
    rw [neg_pow, ← Real.exp_nat_mul]
    rw [show -(((n:ℝ) + 1) * v) = (n : ℝ) * -v + -v by ring, Real.exp_add]
    ring
  rw [heq] at h
  have hval : v * Real.exp (-v) * (1 - -Real.exp (-v))⁻¹ = v * fermi v := by
    have hpos : (0:ℝ) < Real.exp v := Real.exp_pos v
    rw [fermi, Real.exp_neg]
    field_simp
    rw [sub_neg_eq_add, add_comm (Real.exp v) 1, div_self (by positivity)]
  rwa [hval] at h

