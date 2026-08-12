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
noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => (1 / 2 : ℂ) * Complex.I ^ ((j : ℕ) * (k : ℕ))

/-- The normalization constant `1/2` is `1/√(2^2)`, and `I = exp(2πI/4)` is the primitive
4-th root of unity used by the 2-qubit QFT. -/
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
theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, qft2, Fin.sum_univ_succ, pow_succ,
      Complex.I_mul_I, Complex.ext_iff] <;> norm_num

/-- Explicit form of unitarity: `qft2ᴴ * qft2 = 1`. -/
theorem qft2_conjTranspose_mul_self : Matrix.conjTranspose qft2 * qft2 = 1 :=
  Unitary.star_mul_self_of_mem qft_unitary_2

/-- Explicit form of unitarity: `qft2 * qft2ᴴ = 1`. -/
theorem qft2_mul_conjTranspose : qft2 * Matrix.conjTranspose qft2 = 1 :=
  Unitary.mul_star_self_of_mem qft_unitary_2

end QC

