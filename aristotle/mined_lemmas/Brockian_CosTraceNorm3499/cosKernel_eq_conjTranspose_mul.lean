import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

open Matrix

/-- The trace norm (Schatten `1`-norm) of a Hermitian complex matrix: the sum of the absolute
values of its eigenvalues.  (It is set to `0` on non-Hermitian matrices, which we never use.) -/

theorem cosKernel_eq_conjTranspose_mul {N m : ℕ} {c w : Fin m → ℝ} (hc : ∀ k, 0 ≤ c k)
    (x : Fin N → ℝ) :
    cosKernel c w x = (cosFactor c w x)ᴴ * cosFactor c w x := by
  ext i j
  simp only [cosKernel, Matrix.mul_apply, Matrix.conjTranspose_apply, cosFactor, RCLike.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  norm_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hsq : Real.sqrt (c k) * Real.sqrt (c k) = c k := Real.mul_self_sqrt (hc k)
  simp only [Fin.sum_univ_two, mul_sub]
  norm_num [Real.cos_sub]
  linear_combination (Real.cos (w k * x i) * Real.cos (w k * x j)
    + Real.sin (w k * x i) * Real.sin (w k * x j)) * hsq.symm

