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

set_option grind.warning false

namespace QC

/-- The `N × N` Quantum Fourier Transform matrix:
`(QFT N) j k = exp (2 π i j k / N) / √N`. -/

theorem qft_mem_unitaryGroup (hN : N ≠ 0) :
    qft N ∈ Matrix.unitaryGroup (Fin N) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (qft_conjTranspose_mul_self hN)

end

/-- The `8 × 8` QFT matrix (the QFT on 3 qubits) is unitary. -/
