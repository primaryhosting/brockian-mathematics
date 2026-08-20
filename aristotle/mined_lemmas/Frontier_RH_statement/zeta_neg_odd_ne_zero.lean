import Mathlib

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

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Frontier

/-- `s` is a *nontrivial zero* of the Riemann zeta function if `ζ s = 0` and `s` is not one of
the *trivial zeros* `-2, -4, -6, …`. -/

theorem zeta_neg_odd_ne_zero (k : ℕ) : riemannZeta (-(2 * (k : ℂ) + 1)) ≠ 0 := by
  have hre : (2 * (k : ℂ) + 2).re = 2 * k + 2 := by simp
  have hs1 : ∀ n : ℕ, (2 * (k : ℂ) + 2) ≠ -n := by
    intro n h
    have h2 := congrArg Complex.re h
    rw [hre] at h2
    simp at h2
    nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n]
  have hs2 : (2 * (k : ℂ) + 2) ≠ 1 := by
    intro h
    have h2 := congrArg Complex.re h
    rw [hre] at h2
    simp at h2
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have key := riemannZeta_one_sub hs1 hs2
  have h1s : (1 : ℂ) - (2 * (k : ℂ) + 2) = -(2 * (k : ℂ) + 1) := by ring
  rw [h1s] at key
  rw [key]
  have hcos : Complex.cos ((Real.pi : ℂ) * (2 * (k : ℂ) + 2) / 2) = ((-1 : ℝ) ^ (k + 1) : ℝ) := by
    have h : (Real.pi : ℂ) * (2 * (k : ℂ) + 2) / 2 = ((((k + 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_) ?_
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨two_ne_zero, by exact_mod_cast Real.pi_ne_zero⟩)
  · exact Complex.Gamma_ne_zero hs1
  · rw [hcos]; simp
  · refine riemannZeta_ne_zero_of_one_le_re ?_
    rw [hre]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- A nontrivial zero is never a nonpositive integer. -/
