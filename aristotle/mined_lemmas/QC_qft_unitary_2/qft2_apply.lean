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

namespace QC

/-- The 2-qubit quantum Fourier transform matrix, acting on the 4-dimensional state space.
Its `(j, k)` entry is `(1/2) * ω ^ (j * k)` where `ω = exp(2 * π * I / 4) = I` is a primitive
4-th root of unity. -/

theorem qft2_apply (j k : Fin 4) :
    qft2 j k = (1 / Real.sqrt 4 : ℝ) * Complex.exp (2 * Real.pi * Complex.I / 4) ^
      ((j : ℕ) * (k : ℕ)) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hexp : Complex.exp (2 * Real.pi * Complex.I / 4) = Complex.I := by
    have : (2 * (Real.pi : ℂ) * Complex.I / 4) = (Real.pi / 2 : ℝ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I]
    simp
  simp [qft2, h4, hexp]

/-- **The 2-qubit QFT matrix is unitary.** -/
