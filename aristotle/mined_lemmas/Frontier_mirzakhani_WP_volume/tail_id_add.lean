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

lemma tail_id_add (a : ℝ) (ha : 0 ≤ a) :
    (∫ v in Ioi a, v * fermi v) + (∫ v in Ioi (-a), v * fermi v)
      = Real.pi ^ 2 / 6 - a ^ 2 / 2 := by
  have hle : -a ≤ a := by linarith
  have hd : ∀ p : ℝ, Disjoint (Ioc p a) (Ioi a) := fun p => Ioc_disjoint_Ioi le_rfl
  have h1 : ∫ v in Ioi (-a), v * fermi v
      = (∫ v in Ioc (-a) a, v * fermi v) + ∫ v in Ioi a, v * fermi v := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hle,
      setIntegral_union (hd _) measurableSet_Ioi
        ((integrableOn_id_mul_fermi (-a)).mono_set Ioc_subset_Ioi_self)
        (integrableOn_id_mul_fermi a)]
  have h2 : ∫ v in Ioi (0:ℝ), v * fermi v
      = (∫ v in Ioc (0:ℝ) a, v * fermi v) + ∫ v in Ioi a, v * fermi v := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha,
      setIntegral_union (hd _) measurableSet_Ioi
        ((integrableOn_id_mul_fermi 0).mono_set Ioc_subset_Ioi_self)
        (integrableOn_id_mul_fermi a)]
  have h3 : ∫ v in Ioc (-a) a, v * fermi v = ∫ v in (-a)..a, v * fermi v :=
    (intervalIntegral.integral_of_le hle).symm
  have h4 : ∫ v in Ioc (0:ℝ) a, v * fermi v = ∫ v in (0:ℝ)..a, v * fermi v :=
    (intervalIntegral.integral_of_le ha).symm
  have h5 := intervalIntegral_symm_id_mul_fermi a
  have h6 := integral_Ioi_zero_id_mul_fermi
  rw [h3] at h1
  rw [h4] at h2
  linarith

