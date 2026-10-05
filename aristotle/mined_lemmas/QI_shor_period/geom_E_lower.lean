/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module doc-comment `/-! ... -/` before `import`,
-- so the required header appears above as an ordinary block comment.)

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Elementary trigonometric estimates -/

/-- A crude but explicit linear lower bound for `sin` on `[0, 5π/8]`. -/

theorem geom_E_lower (θ : ℝ) (A : ℕ) (h : |θ| * A ≤ 5 * Real.pi / 4) :
    (2 / 5) * (A : ℝ) ≤ ‖∑ j ∈ Finset.range A, E (θ * j)‖ := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hθ : |θ| ≤ 5 * Real.pi / 4 := by
    nlinarith [abs_nonneg θ, Real.pi_pos]
  rcases eq_or_ne θ 0 with rfl | hθ0
  · simp only [zero_mul, E_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Complex.norm_natCast]
    linarith
  · have hne : E θ ≠ 1 := by
      intro hEq
      have : ‖E θ - 1‖ = 0 := by rw [hEq]; simp
      have hlow := norm_E_sub_one_ge θ hθ
      rw [this] at hlow
      have : |θ| ≤ 0 := by linarith
      exact hθ0 (abs_eq_zero.mp (le_antisymm this (abs_nonneg θ)))
    have hsum : ∑ j ∈ Finset.range A, E (θ * j) = (E (θ * A) - 1) / (E θ - 1) := by
      have : ∀ j ∈ Finset.range A, E (θ * j) = (E θ) ^ j := fun j _ => E_pow θ j
      rw [Finset.sum_congr rfl this, geom_sum_eq hne, ← E_pow]
    rw [hsum, norm_div]
    have hden : ‖E θ - 1‖ ≤ |θ| := norm_E_sub_one_le θ
    have hnum : (2 / 5) * |θ * A| ≤ ‖E (θ * A) - 1‖ := by
      refine norm_E_sub_one_ge _ ?_
      rw [abs_mul, Nat.abs_cast]
      exact h
    have hdenpos : 0 < ‖E θ - 1‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact hne
    rw [le_div_iff₀ hdenpos]
    have habs : |θ * (A : ℝ)| = |θ| * A := by
      rw [abs_mul, Nat.abs_cast]
    rw [habs] at hnum
    calc (2 / 5) * (A : ℝ) * ‖E θ - 1‖ ≤ (2 / 5) * (A : ℝ) * |θ| := by
          apply mul_le_mul_of_nonneg_left hden (by positivity)
      _ = (2 / 5) * (|θ| * A) := by ring
      _ ≤ ‖E (θ * A) - 1‖ := hnum

