import Mathlib

/-!
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
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

open Module Polynomial

/-! ## The analytic index

The *analytic index* of an operator `D` is `dim ker D - dim coker D`.  This is the
standard Fredholm index, written here for a `ℂ`-linear map between arbitrary
`ℂ`-vector spaces; it is the meaningful invariant exactly when both the kernel and
the cokernel are finite dimensional (`Module.finrank` returns `0` on infinite
dimensional spaces). -/

/-- The analytic (Fredholm) index `dim ker D - dim coker D` of a linear operator `D`. -/

theorem symbolWinding_eq (n : ℕ) : symbolWinding n = (n : ℂ) := by
  have hEq : Set.EqOn (fun z : ℂ => deriv (fun w : ℂ => w ^ n) z / z ^ n)
      (fun z : ℂ => (n : ℂ) * (z - 0)⁻¹) (Metric.sphere (0 : ℂ) 1) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      simp only [Metric.mem_sphere, dist_zero_right] at hz
      intro h
      rw [h] at hz
      simp at hz
    have hd : deriv (fun w : ℂ => w ^ n) z = (n : ℂ) * z ^ (n - 1) := by simp
    simp only [hd, sub_zero]
    rcases n with _ | m
    · simp
    · rw [pow_succ, Nat.add_sub_cancel]
      field_simp
  unfold symbolWinding
  rw [circleIntegral.integral_congr zero_le_one hEq, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_center_inv 0 one_ne_zero]
  have h : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp

/-- The kernel of multiplication by `X ^ n` on `ℂ[X]` is trivial. -/
