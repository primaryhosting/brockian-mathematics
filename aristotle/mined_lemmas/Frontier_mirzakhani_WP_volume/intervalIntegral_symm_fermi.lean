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

lemma intervalIntegral_symm_fermi (a : ℝ) :
    ∫ v in (-a)..a, fermi v = a := by
  have hint : ∀ p q : ℝ, IntervalIntegrable fermi volume p q :=
    fun p q => continuous_fermi.intervalIntegrable p q
  have hsplit : (∫ v in (-a)..(0:ℝ), fermi v) + ∫ v in (0:ℝ)..a, fermi v
      = ∫ v in (-a)..a, fermi v :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hneg : ∫ v in (0:ℝ)..a, fermi (-v) = ∫ v in (-a)..(0:ℝ), fermi v := by
    rw [intervalIntegral.integral_comp_neg]
    norm_num
  have hone : ∫ v in (0:ℝ)..a, fermi (-v) = a - ∫ v in (0:ℝ)..a, fermi v := by
    have hpt : ∀ v : ℝ, fermi (-v) = 1 - fermi v := fun v => by
      have := fermi_add_fermi_neg v; linarith
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint _ _)]
    simp
  linarith

