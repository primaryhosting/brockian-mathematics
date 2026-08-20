/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A primitive `16`-th root of unity, `exp (2πi/16)`. -/

theorem qftQubits4_unitary :
    qftQubits4 ∈ Matrix.unitaryGroup (Fin 4 → Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star qftQubits4 = (star qftMatrix4).submatrix qubits4Equiv qubits4Equiv := by
    ext i j
    simp [qftQubits4, Matrix.star_apply]
  rw [hstar, qftQubits4, Matrix.submatrix_mul_equiv,
    Matrix.mem_unitaryGroup_iff.mp qft_unitary_4, Matrix.submatrix_one_equiv]

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

