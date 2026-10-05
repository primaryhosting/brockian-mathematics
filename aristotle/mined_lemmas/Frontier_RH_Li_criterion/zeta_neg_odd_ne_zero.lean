/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Complex Filter

/-! ## Li coefficients of a finite family of zeros -/

/-- The `n`-th **Li coefficient** attached to a finite multiset `Z` of (candidate) zeros:
`λ_n(Z) = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`.  This is the standard Bombieri–Lagarias
expression of Li's coefficients as a sum over the zeros. -/

theorem zeta_neg_odd_ne_zero (k : ℕ) : riemannZeta (-(2 * (k : ℂ) + 1)) ≠ 0 := by
  have hre : ((2 * (k : ℂ) + 2)).re = 2 * (k : ℝ) + 2 := by
    simp
  have hne : ∀ n : ℕ, (2 * (k : ℂ) + 2) ≠ -(n : ℂ) := by
    intro n hcon
    have := congrArg Complex.re hcon
    rw [hre] at this
    simp at this
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hne1 : (2 * (k : ℂ) + 2) ≠ 1 := by
    intro hcon
    have := congrArg Complex.re hcon
    rw [hre] at this
    simp at this
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hfe := riemannZeta_one_sub hne hne1
  have harg : (1 : ℂ) - (2 * (k : ℂ) + 2) = -(2 * (k : ℂ) + 1) := by ring
  rw [harg] at hfe
  rw [hfe]
  -- every factor is nonzero
  have hcos : Complex.cos (↑π * (2 * (k : ℂ) + 2) / 2) ≠ 0 := by
    have : (↑π * (2 * (k : ℂ) + 2) / 2) = ((k : ℂ) + 1) * ↑π := by ring
    rw [this]
    have hnat : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hnat, Complex.cos_nat_mul_pi]
    exact pow_ne_zero _ (by norm_num)
  have hgamma : Complex.Gamma (2 * (k : ℂ) + 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero ?_
    intro n
    exact hne n
  have hcpow : ((2 * (π : ℂ)) ^ (-(2 * (k : ℂ) + 2))) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_ |>.2
    · simp [Real.pi_ne_zero]
    · intro hcon
      have := congrArg Complex.re hcon
      simp at this
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  have hzeta : riemannZeta (2 * (k : ℂ) + 2) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    rw [hre]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨⟨⟨⟨two_ne_zero, hcpow⟩, hgamma⟩, hcos⟩, hzeta⟩

/-- A nontrivial zero of `ζ` is never a nonpositive integer. -/
