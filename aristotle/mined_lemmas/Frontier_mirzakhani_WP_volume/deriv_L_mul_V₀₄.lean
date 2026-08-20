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

lemma deriv_L_mul_V₀₄ (L₁ L₂ L₃ L₄ : ℝ) :
    deriv (fun s => s * V₀₄ s L₂ L₃ L₄) L₁
      = 2 * Real.pi ^ 2 + (3 * L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2 := by
  have hf : (fun s => s * V₀₄ s L₂ L₃ L₄)
      = fun s : ℝ => 2 * Real.pi ^ 2 * s + s ^ 3 / 2 + ((L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) * s := by
    funext s; simp only [V₀₄]; ring
  have h1 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * L₁ ^ 2) L₁ := by
    simpa using hasDerivAt_pow 3 L₁
  have h : HasDerivAt
      (fun s : ℝ => 2 * Real.pi ^ 2 * s + s ^ 3 / 2 + ((L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) * s)
      (2 * Real.pi ^ 2 + 3 * L₁ ^ 2 / 2 + (L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) L₁ := by
    have := (((hasDerivAt_id L₁).const_mul (2 * Real.pi ^ 2)).add (h1.div_const 2)).add
      ((hasDerivAt_id L₁).const_mul ((L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2))
    simpa using this
  rw [hf, h.deriv]; ring

/-- Mirzakhani's recursion, together with the base case `V_{0,3} = 1`, *determines* the volume
`V_{0,4}`: any function `W` for which `s ↦ s · W (s)` is differentiable and satisfies the
recursion agrees with `V_{0,4}`. -/
