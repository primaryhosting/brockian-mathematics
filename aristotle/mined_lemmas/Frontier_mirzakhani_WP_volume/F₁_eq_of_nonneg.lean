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

lemma F₁_eq_of_nonneg {t : ℝ} (ht : 0 ≤ t) : F₁ t = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3 := by
  have ha : (0:ℝ) ≤ t / 2 := by linarith
  have hsplit : F₁ t = (∫ x in Ioi (0:ℝ), x * fermi (x / 2 + t / 2))
      + ∫ x in Ioi (0:ℝ), x * fermi (x / 2 + (-(t / 2))) := by
    rw [F₁, ← integral_add (integrableOn_id_mul_fermi_half (t/2) 0)
      (integrableOn_id_mul_fermi_half (-(t/2)) 0)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [mirzakhaniH, show (x + t)/2 = x/2 + t/2 by ring,
      show (x - t)/2 = x/2 + (-(t/2)) by ring]
    ring
  rw [hsplit, integral_shift_fermi (t/2), integral_shift_fermi (-(t/2))]
  have h1 := tail_id_add (t/2) ha
  have h2 := tail_fermi_sub (t/2) ha
  linear_combination 4 * h1 + 2 * t * h2

