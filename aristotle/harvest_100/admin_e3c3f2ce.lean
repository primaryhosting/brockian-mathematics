import Mathlib
/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
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

open scoped Matrix

namespace QC

/-- The 2-qubit quantum Fourier transform matrix, acting on the `4`-dimensional state space.
Its `(j, k)` entry is `(1/√4) * ω ^ (j * k)` where `ω = Complex.exp (2 * π * I / 4) = I`,
i.e. `(1/2) * I ^ (j * k)`. -/
noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => (1 / 2 : ℂ) * Complex.I ^ (j.val * k.val)

/-- `qft2 * qft2ᴴ = 1`. -/
theorem qft2_mul_conjTranspose : qft2 * qft2ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, qft2, Fin.sum_univ_four, Complex.ext_iff, pow_succ,
      Complex.I_mul_I] <;> norm_num

/-- `qft2ᴴ * qft2 = 1`. -/
theorem conjTranspose_mul_qft2 : qft2ᴴ * qft2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, qft2, Fin.sum_univ_four, Complex.ext_iff, pow_succ,
      Complex.I_mul_I] <;> norm_num

/-- **The 2-qubit QFT matrix is unitary.** -/
theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact qft2_mul_conjTranspose

end QC

