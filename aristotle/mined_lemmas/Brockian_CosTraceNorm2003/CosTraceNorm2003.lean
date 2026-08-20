/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The squared Frobenius (Hilbert–Schmidt) norm of a square real matrix:
the sum of the squares of all its entries. -/

theorem CosTraceNorm2003 (θ : ℝ) :
    (rot θ).trace = 2 * Real.cos θ ∧
    |(rot θ).trace| ≤ Real.sqrt 2 * Real.sqrt (frobSq (rot θ)) ∧
    Real.sqrt 2 * Real.sqrt (frobSq (rot θ)) = 2 ∧
    |2 * Real.cos θ| ≤ 2 ∧
    (|2 * Real.cos θ| = 2 ↔ ∃ k : ℤ, θ = k * Real.pi) := by
  have hn : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
  have hb : |(rot θ).trace| ≤ Real.sqrt 2 * Real.sqrt (frobSq (rot θ)) := by
    have := abs_trace_le_sqrt_mul_sqrt_frobSq (rot θ)
    rwa [hn] at this
  have hrhs : Real.sqrt 2 * Real.sqrt (frobSq (rot θ)) = 2 := by
    rw [frobSq_rot]
    exact Real.mul_self_sqrt (by norm_num)
  refine ⟨trace_rot θ, hb, hrhs, ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have := Real.abs_cos_le_one θ
    linarith
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    constructor
    · intro h
      have hc : |Real.cos θ| = 1 := by linarith
      have hs : Real.sin θ = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq θ, sq_abs (Real.cos θ), sq_nonneg (Real.sin θ)]
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hs
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, rfl⟩
      have : Real.sin (k * Real.pi) = 0 := by
        simp [Real.sin_int_mul_pi k]
      have hcos : Real.cos ((k : ℝ) * Real.pi) ^ 2 = 1 := by
        nlinarith [Real.sin_sq_add_cos_sq ((k : ℝ) * Real.pi)]
      have : |Real.cos ((k : ℝ) * Real.pi)| = 1 := by
        have := sq_abs (Real.cos ((k : ℝ) * Real.pi))
        nlinarith [abs_nonneg (Real.cos ((k : ℝ) * Real.pi))]
      rw [this]; ring

/-! ### Extension of the family: trace bounds for orthogonal matrices -/

/-- An orthogonal matrix has squared Frobenius norm equal to its size. -/
