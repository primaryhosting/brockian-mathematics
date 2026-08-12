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

set_option grind.warning false

namespace QC

open Matrix

/-- The `2`-qubit quantum Fourier transform matrix on the computational basis
`Fin 4`: its `(j, k)` entry is `(1/2) * ω ^ (j * k)`, where `ω = exp (2 π i / 4) = i`
is a primitive fourth root of unity. -/
noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun j k => (1 / 2 : ℂ) * Complex.I ^ (j.val * k.val)

/-- The 2-qubit QFT matrix is unitary. -/
theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, qft2, pow_succ, Complex.ext_iff] <;> ring_nf

/-- Unitarity of the 2-qubit QFT, spelled out as `Uᴴ * U = 1`. -/
theorem qft2_conjTranspose_mul_self : qft2ᴴ * qft2 = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp qft_unitary_2

/-- Unitarity of the 2-qubit QFT, spelled out as `U * Uᴴ = 1`. -/
theorem qft2_mul_conjTranspose_self : qft2 * qft2ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp qft_unitary_2

end QC

