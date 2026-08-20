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

theorem mirzakhani_WP_volume :
    (∀ L₁ L₂ L₃ : ℝ, V₀₃ L₁ L₂ L₃ = 1) ∧
    (∀ t : ℝ, ∫ x in Ioi (0:ℝ), x * mirzakhaniH x t = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3) ∧
    (∀ L₁ L₂ L₃ L₄ : ℝ,
      deriv (fun s => s * V₀₄ s L₂ L₃ L₄) L₁ = mirzakhaniRHS₀₄ L₁ L₂ L₃ L₄) ∧
    (∀ (L₂ L₃ L₄ : ℝ) (W : ℝ → ℝ), Differentiable ℝ (fun s => s * W s) →
      (∀ s : ℝ, deriv (fun r => r * W r) s = mirzakhaniRHS₀₄ s L₂ L₃ L₄) →
      ∀ s : ℝ, s * W s = s * V₀₄ s L₂ L₃ L₄) := by
  refine ⟨fun _ _ _ => rfl, fun t => F₁_eq t, fun L₁ L₂ L₃ L₄ => ?_,
    fun L₂ L₃ L₄ W hW hrec => V₀₄_of_recursion L₂ L₃ L₄ W hW hrec⟩
  rw [deriv_L_mul_V₀₄, mirzakhaniRHS₀₄_eq]

end Frontier

