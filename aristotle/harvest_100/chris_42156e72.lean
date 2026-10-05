/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian

/-- The planar rotation matrix by angle `θ`. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Rotations compose by adding angles. -/
theorem rot_mul (θ φ : ℝ) : rot θ * rot φ = rot (θ + φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

/-- Powers of a rotation are rotations. -/
theorem rot_pow (θ : ℝ) : ∀ n : ℕ, (rot θ) ^ n = rot (n * θ)
  | 0 => by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rot, Matrix.one_apply]
  | (n + 1) => by
      rw [pow_succ, rot_pow θ n, rot_mul]
      push_cast
      ring_nf

/-- The trace of a rotation matrix. -/
theorem trace_rot (θ : ℝ) : Matrix.trace (rot θ) = 2 * Real.cos θ := by
  simp [rot, Matrix.trace_fin_two_of]
  ring

/-- The trace of a power of a rotation matrix. -/
theorem trace_rot_pow (θ : ℝ) (n : ℕ) :
    Matrix.trace ((rot θ) ^ n) = 2 * Real.cos (n * θ) := by
  rw [rot_pow, trace_rot]

/-- `|cos x| = 1` exactly when `sin x = 0`. -/
theorem abs_cos_eq_one_iff (x : ℝ) : |Real.cos x| = 1 ↔ Real.sin x = 0 := by
  constructor
  · intro h
    have h2 : Real.cos x ^ 2 = 1 := by
      have := congrArg (fun t : ℝ => t ^ 2) h
      simpa [sq_abs] using this
    have := Real.sin_sq_add_cos_sq x
    nlinarith [this, h2]
  · intro h
    have h2 : Real.cos x ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq x
      rw [h] at this
      nlinarith [this]
    have : |Real.cos x| ^ 2 = 1 := by simpa [sq_abs] using h2
    nlinarith [abs_nonneg (Real.cos x), this]

/--
**Cos Trace Norm 1279.**

For every angle `θ` and every exponent `n`, the `n`-th power of the planar rotation
`rot θ` is the rotation by `n * θ`, its trace equals `2 * cos (n * θ)`, this trace is
bounded in absolute value by `2`, and the bound is attained exactly when
`sin (n * θ) = 0`.  Moreover the bound is strict in the complementary case.
-/
theorem CosTraceNorm1279 (θ : ℝ) (n : ℕ) :
    Matrix.trace ((rot θ) ^ n) = 2 * Real.cos (n * θ) ∧
    |Matrix.trace ((rot θ) ^ n)| ≤ 2 ∧
    (|Matrix.trace ((rot θ) ^ n)| = 2 ↔ Real.sin (n * θ) = 0) ∧
    (Real.sin (n * θ) ≠ 0 → |Matrix.trace ((rot θ) ^ n)| < 2) := by
  have htr : Matrix.trace ((rot θ) ^ n) = 2 * Real.cos (n * θ) := trace_rot_pow θ n
  have habs : |Matrix.trace ((rot θ) ^ n)| = 2 * |Real.cos (n * θ)| := by
    rw [htr, abs_mul]
    norm_num
  have hle : |Real.cos ((n : ℝ) * θ)| ≤ 1 := Real.abs_cos_le_one _
  refine ⟨htr, ?_, ?_, ?_⟩
  · rw [habs]; linarith
  · rw [habs]
    constructor
    · intro h
      exact (abs_cos_eq_one_iff _).mp (by linarith)
    · intro h
      rw [(abs_cos_eq_one_iff _).mpr h]
      norm_num
  · intro h
    rw [habs]
    rcases lt_or_eq_of_le hle with hlt | heq
    · linarith
    · exact absurd ((abs_cos_eq_one_iff _).mp heq) h

end Brockian

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

