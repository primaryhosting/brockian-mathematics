import Brockian.Equidistribution

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
# Weyl equidistribution

This file develops, from scratch, Weyl's criterion for equidistribution modulo one and applies
it to the sequence `n ↦ n * α` for irrational `α`.

The main statement is `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`, which
is *conditional* on the asymptotic vanishing of the Weyl exponential sums, and its unconditional
consequence `Brockian.Equidistribution.equidistributedMod1_natMul_irrational`.
-/

namespace Brockian.Equidistribution

open MeasureTheory Filter Finset Complex Topology Metric

open scoped Real

noncomputable section

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem integral_fourier_eq_zero {h : ℤ} (hh : h ≠ 0) :
    (∫ z : AddCircle (1 : ℝ), fourier h z) = 0 := by
  rw [← AddCircle.intervalIntegral_preimage 1 0]
  simp only [fourier_coe_apply]
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => Complex.exp (2 * π * I * h * x))
    (fun x _ => by push_cast; ring_nf)]
  rw [integral_exp_mul_complex (by simp [Real.pi_ne_zero, hh, Complex.ext_iff])]
  norm_num
  left
  rw [sub_eq_zero, Complex.exp_eq_one_iff]
  exact ⟨h, by ring⟩

