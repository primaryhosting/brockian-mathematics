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

theorem V₀₄_of_recursion (L₂ L₃ L₄ : ℝ) (W : ℝ → ℝ)
    (hW : Differentiable ℝ (fun s => s * W s))
    (hrec : ∀ s : ℝ, deriv (fun r => r * W r) s = mirzakhaniRHS₀₄ s L₂ L₃ L₄) (s : ℝ) :
    s * W s = s * V₀₄ s L₂ L₃ L₄ := by
  have hdiffV : Differentiable ℝ (fun r : ℝ => r * V₀₄ r L₂ L₃ L₄) := by
    have hpoly : (fun r : ℝ => r * V₀₄ r L₂ L₃ L₄)
        = fun r : ℝ => 2 * Real.pi ^ 2 * r + r ^ 3 / 2 + ((L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) * r := by
      funext r; simp only [V₀₄]; ring
    rw [hpoly]; fun_prop
  have hg : Differentiable ℝ (fun r : ℝ => r * W r - r * V₀₄ r L₂ L₃ L₄) := hW.sub hdiffV
  have hderiv : ∀ r : ℝ, deriv (fun r : ℝ => r * W r - r * V₀₄ r L₂ L₃ L₄) r = 0 := by
    intro r
    have h1 : HasDerivAt (fun q : ℝ => q * W q) (mirzakhaniRHS₀₄ r L₂ L₃ L₄) r := by
      have hd := (hW r).hasDerivAt
      rwa [hrec r] at hd
    have h2 : HasDerivAt (fun q : ℝ => q * V₀₄ q L₂ L₃ L₄) (mirzakhaniRHS₀₄ r L₂ L₃ L₄) r := by
      have hd := (hdiffV r).hasDerivAt
      rwa [deriv_L_mul_V₀₄ r L₂ L₃ L₄, ← mirzakhaniRHS₀₄_eq] at hd
    simpa using (h1.sub h2).deriv
  have hconst := is_const_of_deriv_eq_zero hg hderiv s 0
  simp only [zero_mul, sub_self] at hconst
  linarith

/-- **Mirzakhani's recursion for Weil–Petersson volumes**, base case and first step.

1. (Base case.)  The Weil–Petersson volume of the moduli space of bordered pairs of pants is
   `V_{0,3} ≡ 1`, independently of the boundary lengths.
2. (First moment of the kernel.)  Mirzakhani's kernel has first moment
   `∫₀^∞ x H (x, t) dx = t² / 2 + 2 π² / 3`.
3. (Recursion, and uniqueness of its solution.)  The volume polynomial
   `V_{0,4} (L) = 2 π² + (∑ Lᵢ²) / 2` satisfies Mirzakhani's recursion
   `∂/∂L₁ (L₁ · V_{0,4} (L)) = ½ ∑_{j = 2}^{4} ∫₀^∞ x (H (x, L₁ + L_j) + H (x, L₁ - L_j))
      V_{0,3} (x, …) dx`,
   whose right-hand side is built from the base case `V_{0,3}` alone (the two "pair of pants"
   terms of the general recursion are empty in this case for stability reasons). -/
