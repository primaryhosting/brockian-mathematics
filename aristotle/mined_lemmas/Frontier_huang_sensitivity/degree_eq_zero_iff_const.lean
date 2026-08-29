/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/

lemma degree_eq_zero_iff_const {n : ℕ} (f : (Fin n → Bool) → Bool) :
    degree f = 0 ↔ ∀ x y, f x = f y := by
  constructor
  · intro h x y
    have hzero : ∀ S : Finset (Fin n), S ≠ ∅ → fourierCoeff f S = 0 := by
      intro S hS
      by_contra hc
      have hmem : S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun S => fourierCoeff f S ≠ 0) := by simp [hc]
      have hcard : S.card ≤ degree f := Finset.le_sup hmem
      rw [h, Nat.le_zero, Finset.card_eq_zero] at hcard
      exact hS hcard
    have hval : ∀ z : Fin n → Bool,
        2 ^ n * (if f z then (-1 : ℤ) else 1) = fourierCoeff f ∅ := by
      intro z
      rw [← sum_coeff_mul_chi f z, Finset.sum_eq_single (∅ : Finset (Fin n))]
      · rw [chi_empty, mul_one]
      · intro S _ hS
        rw [hzero S hS, zero_mul]
      · intro hc
        exact absurd (Finset.mem_univ (∅ : Finset (Fin n))) hc
    have h2 : (2 : ℤ) ^ n * (if f x then (-1 : ℤ) else 1)
        = 2 ^ n * (if f y then (-1 : ℤ) else 1) := by rw [hval x, hval y]
    have hpow : (0 : ℤ) < 2 ^ n := by positivity
    have hcancel := mul_left_cancel₀ (ne_of_gt hpow) h2
    revert hcancel
    cases hx : f x <;> cases hy : f y <;> simp
  · intro h
    apply Nat.le_zero.1
    apply Finset.sup_le
    intro S hS
    simp only [Finset.mem_filter] at hS
    have hempty : S = ∅ := by
      by_contra hne
      apply hS.2
      have hconst : ∀ y : Fin n → Bool, (if f y then (-1 : ℤ) else 1)
          = (if f (fun _ => false) then (-1 : ℤ) else 1) := by
        intro y; rw [h y (fun _ => false)]
      simp only [fourierCoeff, hconst, ← Finset.mul_sum, sum_chi, if_neg hne, mul_zero]
    simp [hempty]

/-! ## Degree at most one and sensitivity at most one -/

