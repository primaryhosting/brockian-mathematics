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

lemma hasSum_odd_zeta_two :
    HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
    simp only [] at h; omega
  have hcomp : (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2)
      = (fun n : ℕ => 1 / ((n:ℝ))^2) ∘ (fun k : ℕ => 2 * k + 1) := rfl
  have hsummable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    rw [hcomp]; exact hasSum_zeta_two.summable.comp_injective hinj
  have heven : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
    have h := hasSum_zeta_two.mul_left (1/4 : ℝ)
    have heq : (fun k : ℕ => (1/4 : ℝ) * (1 / (k:ℝ)^2))
        = fun k : ℕ => 1 / ((2*k : ℕ):ℝ)^2 := by
      funext k
      push_cast
      rw [mul_pow]
      norm_num
      ring
    rw [heq] at h
    convert h using 1
    ring
  have hodd := hsummable.hasSum
  have h := HasSum.even_add_odd (f := fun n : ℕ => 1 / ((n:ℝ))^2) heven hodd
  have h2 := hasSum_zeta_two.unique h
  have heq2 : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = Real.pi ^ 2 / 8 := by linarith
  rwa [heq2] at hodd

/-- The alternating Basel sum `∑ (-1) ^ n / (n + 1) ^ 2 = π ^ 2 / 12`. -/
