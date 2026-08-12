import Mathlib
/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 2-qubit quantum Fourier transform matrix: the `4 × 4` matrix with entries
`(1/2) * ω ^ (j * k)`, where `ω = exp (2 * π * I / 4) = I` is a primitive 4-th root of unity. -/
noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => (1 / 2 : ℂ) * Complex.I ^ (j.val * k.val)

/-- The entries of `qft2` are the usual QFT entries `(1/√4) * exp (2πi·jk/4)`. -/
theorem qft2_apply_exp (j k : Fin 4) :
    qft2 j k = (1 / 2 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / 4) := by
  have h : Complex.exp (2 * Real.pi * Complex.I / 4) = Complex.I := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I / 4) = (Real.pi / 2 : ℝ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp
  rw [qft2]
  congr 1
  conv_lhs => rw [← h]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The 2-qubit QFT matrix is unitary. -/
theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, qft2, Fin.sum_univ_four, Matrix.star_apply,
      pow_succ, Complex.ext_iff] <;> norm_num

end QC

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

