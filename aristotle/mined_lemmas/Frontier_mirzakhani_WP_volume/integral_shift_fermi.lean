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

lemma integral_shift_fermi (d : ℝ) :
    ∫ x in Ioi (0:ℝ), x * fermi (x / 2 + d)
      = 4 * ((∫ v in Ioi d, v * fermi v) - d * ∫ v in Ioi d, fermi v) := by
  have hscale : ∫ x in Ioi (0:ℝ), x * fermi (x / 2 + d)
      = 4 * ∫ u in Ioi (0:ℝ), u * fermi (u + d) := by
    have h := integral_comp_mul_left_Ioi (fun y : ℝ => 2 * y * fermi (y + d)) 0
      (b := 1/2) (by norm_num)
    simp only [smul_eq_mul] at h
    rw [show ((1:ℝ)/2 * 0) = 0 by ring] at h
    have hl : ∫ x in Ioi (0:ℝ), 2 * ((1:ℝ)/2 * x) * fermi ((1:ℝ)/2 * x + d)
        = ∫ x in Ioi (0:ℝ), x * fermi (x / 2 + d) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      rw [show (2:ℝ) * ((1:ℝ)/2 * x) = x by ring, show (1:ℝ)/2 * x = x / 2 by ring]
    rw [hl] at h
    rw [h]
    have hc : ∫ y in Ioi (0:ℝ), 2 * y * fermi (y + d)
        = 2 * ∫ y in Ioi (0:ℝ), y * fermi (y + d) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
    rw [hc]
    ring
  have htrans : ∫ u in Ioi (0:ℝ), u * fermi (u + d)
      = ∫ v in Ioi d, (v - d) * fermi v := by
    have h := (measurePreserving_add_right (volume : Measure ℝ) d).setIntegral_preimage_emb
      (measurableEmbedding_addRight d) (fun v => (v - d) * fermi v) (Ioi d)
    have hpre : (fun x : ℝ => x + d) ⁻¹' (Ioi d) = Ioi (0:ℝ) := by
      ext x; simp [Set.mem_Ioi]
    rw [hpre] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring_nf)
  have hsplit : ∫ v in Ioi d, (v - d) * fermi v
      = (∫ v in Ioi d, v * fermi v) - d * ∫ v in Ioi d, fermi v := by
    have hi1 := integrableOn_id_mul_fermi d
    have hi2 := (integrableOn_fermi d).const_mul d
    rw [← integral_const_mul, ← integral_sub hi1 hi2]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  rw [hscale, htrans, hsplit]

/-! ## Evaluation of the first moment of Mirzakhani's kernel -/

