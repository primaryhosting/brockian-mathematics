/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

/-! ## The 2D Ising model on a finite torus -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem sub_mul_cos_eq_norm_mul (a b r r' : ℝ) (hb0 : b ≠ 0) (ha : |b| < a)
    (hrr' : r * r' = 1) (hsum : r + r' = 2 * a / b) (θ : ℝ) :
    a - b * Real.cos θ
      = |b| / 2 * ‖circleMap 0 1 θ - (r : ℂ)‖ * ‖circleMap 0 1 θ - (r' : ℂ)‖ := by
  have hznorm : ‖circleMap 0 1 θ‖ = 1 := by simp
  have hz0 : circleMap 0 1 θ ≠ 0 := by
    intro h; rw [h] at hznorm; simp at hznorm
  have hzc : circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹ = 2 * (Real.cos θ : ℂ) := by
    have hz : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
    rw [hz, ← Complex.exp_neg,
      show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) * Complex.I) by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_sin]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  have hsum' : (r : ℂ) + (r' : ℂ) = 2 * (a : ℂ) / (b : ℂ) := by
    rw [show (2 : ℂ) * (a : ℂ) / (b : ℂ) = ((2 * a / b : ℝ) : ℂ) by push_cast; ring, ← hsum]
    push_cast; ring
  have hid := factor_of_roots (a : ℂ) (b : ℂ) (Real.cos θ : ℂ) (circleMap 0 1 θ) (r : ℂ) (r' : ℂ)
    (by exact_mod_cast hb0) hz0 hzc (by exact_mod_cast hrr') hsum'
  have hnorm := congrArg (fun w : ℂ => ‖w‖) hid
  simp only [Complex.norm_mul, norm_inv, hznorm] at hnorm
  have hpos : 0 < a - b * Real.cos θ := by
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ, abs_nonneg b, le_abs_self b, neg_abs_le b]
  have hL : ‖(a : ℂ) - (b : ℂ) * (Real.cos θ : ℂ)‖ = a - b * Real.cos θ := by
    rw [show ((a : ℂ) - (b : ℂ) * (Real.cos θ : ℂ)) = ((a - b * Real.cos θ : ℝ) : ℂ) by
        push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  rw [hL] at hnorm
  rw [hnorm]
  simp

/-- Continuity of `θ ↦ log ‖circleMap 0 1 θ - c‖` when `c` is off the unit circle. -/
