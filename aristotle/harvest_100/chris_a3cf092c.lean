/-
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 2-qubit quantum Fourier transform matrix, acting on the 4-dimensional state
space with basis indexed by `Fin 4`.  Its entries are `(1/2) * ω ^ (j * k)` where
`ω = exp(2πi/4) = i` is a primitive 4th root of unity. -/
noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => (1 / 2 : ℂ) * Complex.I ^ ((j : ℕ) * (k : ℕ))

/-- The 2-qubit QFT matrix is unitary. -/
theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, qft2, pow_succ, Complex.ext_iff] <;>
    norm_num [Complex.ext_iff]

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

