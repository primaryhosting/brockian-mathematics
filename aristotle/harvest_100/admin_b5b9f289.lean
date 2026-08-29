import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
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

namespace Brockian

/-- The `cos`-trace: the trace of the `n`-th truncated rotation family,
`∑_{k < n} cos (k x)`. -/
noncomputable def cosTrace (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.cos (k * x)

@[simp] lemma cosTrace_zero (x : ℝ) : cosTrace 0 x = 0 := by
  simp [cosTrace]

lemma cosTrace_succ (n : ℕ) (x : ℝ) :
    cosTrace (n + 1) x = cosTrace n x + Real.cos (n * x) := by
  simp [cosTrace, Finset.sum_range_succ]

/-- Telescoping (Dirichlet-kernel) identity, proved by induction on `n`. -/
lemma two_sin_half_mul_cosTrace (n : ℕ) (x : ℝ) :
    2 * Real.sin (x / 2) * cosTrace n x
      = Real.sin ((2 * (n : ℝ) - 1) * x / 2) + Real.sin (x / 2) := by
  induction n with
  | zero =>
      have h : (2 * ((0 : ℕ) : ℝ) - 1) * x / 2 = -(x / 2) := by push_cast; ring
      rw [h]
      simp
  | succ n ih =>
      have h1 : (2 * ((n + 1 : ℕ) : ℝ) - 1) * x / 2 = (n : ℝ) * x + x / 2 := by
        push_cast; ring
      have h2 : (2 * (n : ℝ) - 1) * x / 2 = (n : ℝ) * x - x / 2 := by ring
      rw [cosTrace_succ, h1]
      rw [h2] at ih
      rw [Real.sin_add]
      nlinarith [ih, Real.sin_sub ((n : ℝ) * x) (x / 2)]

/-- Trivial bound: the `cos`-trace of `n` terms has absolute value at most `n`. -/
lemma abs_cosTrace_le_card (n : ℕ) (x : ℝ) : |cosTrace n x| ≤ (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [cosTrace_succ]
      have h := abs_add_le (cosTrace n x) (Real.cos ((n : ℝ) * x))
      have hc : |Real.cos ((n : ℝ) * x)| ≤ 1 := Real.abs_cos_le_one _
      push_cast
      linarith

/-- Dirichlet bound: away from the zeros of `sin (x/2)`, the `cos`-trace is bounded
independently of `n`. -/
lemma abs_cosTrace_le_inv_abs_sin (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    |cosTrace n x| ≤ 1 / |Real.sin (x / 2)| := by
  have key := two_sin_half_mul_cosTrace n x
  have h1 : |2 * Real.sin (x / 2) * cosTrace n x| ≤ 2 := by
    rw [key]
    calc |Real.sin ((2 * (n : ℝ) - 1) * x / 2) + Real.sin (x / 2)|
        ≤ |Real.sin ((2 * (n : ℝ) - 1) * x / 2)| + |Real.sin (x / 2)| := abs_add_le _ _
      _ ≤ 1 + 1 := by
          have := Real.abs_sin_le_one ((2 * (n : ℝ) - 1) * x / 2)
          have := Real.abs_sin_le_one (x / 2)
          linarith
      _ = 2 := by norm_num
  have habs : (0 : ℝ) < |Real.sin (x / 2)| := abs_pos.mpr hx
  rw [abs_mul, abs_mul, abs_two] at h1
  rw [le_div_iff₀ habs]
  nlinarith [h1, habs]

/-- **Cos Trace Norm 1279.**  For every `n` and every real `x`, the truncated
`cos`-trace `∑_{k < n} cos (k x)` satisfies both the trivial norm bound `n`
and, away from the zeros of `sin (x/2)`, the uniform Dirichlet bound
`1 / |sin (x/2)|`. -/
theorem CosTraceNorm1279 (n : ℕ) (x : ℝ) :
    |cosTrace n x| ≤ (n : ℝ) ∧
      (Real.sin (x / 2) ≠ 0 → |cosTrace n x| ≤ 1 / |Real.sin (x / 2)|) :=
  ⟨abs_cosTrace_le_card n x, fun hx => abs_cosTrace_le_inv_abs_sin n x hx⟩

end Brockian

