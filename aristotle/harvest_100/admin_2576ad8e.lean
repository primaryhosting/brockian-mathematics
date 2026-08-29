import Mathlib
-- (Lean 4 requires `import` lines to precede any module doc comment; the requested
-- header follows immediately below.)
/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Complex

/-- The 2-qubit quantum Fourier transform matrix: the `4 × 4` complex matrix with
entries `(1/2) * i^(j*k)`, where `i` is a primitive 4th root of unity and
`1/2 = 1/√4` is the normalisation factor. -/
noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => (1 / 2 : ℂ) * Complex.I ^ (j.val * k.val)

/-- The 2-qubit QFT matrix is unitary. -/
theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, qft2, Fin.sum_univ_four, pow_succ, Complex.ext_iff] <;>
      norm_num [Complex.I_mul_I]

/-- Explicit form of unitarity: `qft2ᴴ * qft2 = 1`. -/
theorem qft2_conjTranspose_mul_self : qft2ᴴ * qft2 = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp qft_unitary_2

/-- Explicit form of unitarity: `qft2 * qft2ᴴ = 1`. -/
theorem qft2_mul_conjTranspose_self : qft2 * qft2ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp qft_unitary_2

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

