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
`i ^ (j * k) / 2`, where `i` is the primitive fourth root of unity. -/
noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => Complex.I ^ (j.val * k.val) / 2

/-- Explicit description of the 2-qubit QFT matrix. -/
theorem qft2_eq :
    qft2 = (2 : ℂ)⁻¹ •
      !![1, 1, 1, 1;
         1, Complex.I, -1, -Complex.I;
         1, -1, 1, -1;
         1, -Complex.I, -1, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qft2, pow_succ, Complex.I_mul_I] <;> ring

/-- The 2-qubit QFT matrix is unitary. -/
theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', qft2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, map_ofNat] <;>
    ring_nf <;> norm_num [Complex.ext_iff]

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

