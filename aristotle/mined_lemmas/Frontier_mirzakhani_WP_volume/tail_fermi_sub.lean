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

lemma tail_fermi_sub (a : ℝ) (ha : 0 ≤ a) :
    (∫ v in Ioi (-a), fermi v) - (∫ v in Ioi a, fermi v) = a := by
  have hle : -a ≤ a := by linarith
  have h1 : ∫ v in Ioi (-a), fermi v
      = (∫ v in Ioc (-a) a, fermi v) + ∫ v in Ioi a, fermi v := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hle,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((integrableOn_fermi (-a)).mono_set Ioc_subset_Ioi_self)
        (integrableOn_fermi a)]
  have h3 : ∫ v in Ioc (-a) a, fermi v = ∫ v in (-a)..a, fermi v :=
    (intervalIntegral.integral_of_le hle).symm
  rw [h3, intervalIntegral_symm_fermi a] at h1
  linarith

/-! ## Scaling and translation -/

