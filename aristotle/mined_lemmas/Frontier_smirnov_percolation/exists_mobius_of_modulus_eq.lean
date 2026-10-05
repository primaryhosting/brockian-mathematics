/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

namespace Frontier

/-- A real Möbius transformation `x ↦ (a x + b) / (c x + d)`.  These are exactly the
boundary values on `ℝ = ∂ℍ` of the conformal automorphisms of the upper half-plane. -/

theorem exists_mobius_of_modulus_eq {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ}
    (hx : Distinct4 x₁ x₂ x₃ x₄) (hy : Distinct4 y₁ y₂ y₃ y₄)
    (h : modulus x₁ x₂ x₃ x₄ = modulus y₁ y₂ y₃ y₄) :
    ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧
      c * x₁ + d ≠ 0 ∧ c * x₂ + d ≠ 0 ∧ c * x₃ + d ≠ 0 ∧ c * x₄ + d ≠ 0 ∧
      mobius a b c d x₁ = y₁ ∧ mobius a b c d x₂ = y₂ ∧
      mobius a b c d x₃ = y₃ ∧ mobius a b c d x₄ = y₄ := by
  obtain ⟨x12, x13, x14, x23, x24, x34⟩ := hx
  obtain ⟨y12, y13, y14, y23, y24, y34⟩ := hy
  have hx31 : x₃ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm x13)
  have hx32 : x₃ - x₂ ≠ 0 := sub_ne_zero.2 (Ne.symm x23)
  have hx12 : x₁ - x₂ ≠ 0 := sub_ne_zero.2 x12
  have hx21 : x₂ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm x12)
  have hx42 : x₄ - x₂ ≠ 0 := sub_ne_zero.2 (Ne.symm x24)
  have hx41 : x₄ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm x14)
  have hy31 : y₃ - y₁ ≠ 0 := sub_ne_zero.2 (Ne.symm y13)
  have hy32 : y₃ - y₂ ≠ 0 := sub_ne_zero.2 (Ne.symm y23)
  have hy12 : y₁ - y₂ ≠ 0 := sub_ne_zero.2 y12
  have hy42 : y₄ - y₂ ≠ 0 := sub_ne_zero.2 (Ne.symm y24)
  have hy41 : y₄ - y₁ ≠ 0 := sub_ne_zero.2 (Ne.symm y14)
  have hQ : (x₃ - x₂) * (x₄ - x₁) ≠ 0 := mul_ne_zero hx32 hx41
  have hQ' : (y₃ - y₂) * (y₄ - y₁) ≠ 0 := mul_ne_zero hy32 hy41
  rw [modulus, modulus, div_eq_div_iff hQ hQ'] at h
  refine ⟨(-y₂ * (y₃ - y₁)) * (x₃ - x₂) - (-y₁ * (y₃ - y₂)) * (x₃ - x₁),
    (-y₂ * (y₃ - y₁)) * (-x₁ * (x₃ - x₂)) - (-y₁ * (y₃ - y₂)) * (-x₂ * (x₃ - x₁)),
    (y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂),
    (y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ((-y₂ * (y₃ - y₁)) * (x₃ - x₂) - (-y₁ * (y₃ - y₂)) * (x₃ - x₁)) *
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂))) -
        ((-y₂ * (y₃ - y₁)) * (-x₁ * (x₃ - x₂)) - (-y₁ * (y₃ - y₂)) * (-x₂ * (x₃ - x₁))) *
        ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂))
        = ((y₃ - y₂) * (y₃ - y₁) * (y₁ - y₂)) * ((x₃ - x₂) * (x₃ - x₁) * (x₁ - x₂)) := by
      ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hy32 hy31) hy12)
      (mul_ne_zero (mul_ne_zero hx32 hx31) hx12)
  · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₁ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
        = (y₃ - y₂) * ((x₃ - x₁) * (x₁ - x₂)) := by ring
    rw [e]
    exact mul_ne_zero hy32 (mul_ne_zero hx31 hx12)
  · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₂ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
        = -((y₃ - y₁) * ((x₃ - x₂) * (x₂ - x₁))) := by ring
    rw [e]
    exact neg_ne_zero.2 (mul_ne_zero hy31 (mul_ne_zero hx32 hx21))
  · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₃ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
        = (y₁ - y₂) * ((x₃ - x₁) * (x₃ - x₂)) := by ring
    rw [e]
    exact mul_ne_zero hy12 (mul_ne_zero hx31 hx32)
  · -- the fourth point is not the pole: this uses the equality of moduli
    have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₄ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
        = (y₃ - y₂) * ((x₃ - x₁) * (x₄ - x₂)) - (y₃ - y₁) * ((x₃ - x₂) * (x₄ - x₁)) := by
      ring
    rw [e]
    intro hzero
    -- multiply by `(y₃ - y₂) * (y₄ - y₁)` and use the modulus identity
    have h1 : (y₃ - y₂) * (y₃ - y₁) * ((y₄ - y₂) - (y₄ - y₁)) *
        ((x₃ - x₂) * (x₄ - x₁)) = 0 := by
      linear_combination ((y₃ - y₂) * (y₄ - y₁)) * hzero - (y₃ - y₂) * h
    rcases mul_eq_zero.1 h1 with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · rcases mul_eq_zero.1 h3 with h4 | h4
        · exact hy32 h4
        · exact hy31 h4
      · exact hy12 (by linarith)
    · exact hQ h2
  · rw [mobius, div_eq_iff]
    · ring
    · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₁ +
          ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
          = (y₃ - y₂) * ((x₃ - x₁) * (x₁ - x₂)) := by ring
      rw [e]
      exact mul_ne_zero hy32 (mul_ne_zero hx31 hx12)
  · rw [mobius, div_eq_iff]
    · ring
    · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₂ +
          ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
          = -((y₃ - y₁) * ((x₃ - x₂) * (x₂ - x₁))) := by ring
      rw [e]
      exact neg_ne_zero.2 (mul_ne_zero hy31 (mul_ne_zero hx32 hx21))
  · rw [mobius, div_eq_iff]
    · ring
    · have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₃ +
          ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
          = (y₁ - y₂) * ((x₃ - x₁) * (x₃ - x₂)) := by ring
      rw [e]
      exact mul_ne_zero hy12 (mul_ne_zero hx31 hx32)
  · have hden : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₄ +
        ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂))) ≠ 0 := by
      have e : ((y₃ - y₂) * (x₃ - x₁) - (y₃ - y₁) * (x₃ - x₂)) * x₄ +
          ((y₃ - y₂) * (-x₂ * (x₃ - x₁)) - (y₃ - y₁) * (-x₁ * (x₃ - x₂)))
          = (y₃ - y₂) * ((x₃ - x₁) * (x₄ - x₂)) - (y₃ - y₁) * ((x₃ - x₂) * (x₄ - x₁)) := by
        ring
      rw [e]
      intro hzero
      have h1 : (y₃ - y₂) * (y₃ - y₁) * ((y₄ - y₂) - (y₄ - y₁)) *
          ((x₃ - x₂) * (x₄ - x₁)) = 0 := by
        linear_combination ((y₃ - y₂) * (y₄ - y₁)) * hzero - (y₃ - y₂) * h
      rcases mul_eq_zero.1 h1 with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · exact hy32 h4
          · exact hy31 h4
        · exact hy12 (by linarith)
      · exact hQ h2
    rw [mobius, div_eq_iff hden]
    linear_combination -h

/-- Any two quads with the same modulus have the same value under a conformally invariant
crossing function. -/
