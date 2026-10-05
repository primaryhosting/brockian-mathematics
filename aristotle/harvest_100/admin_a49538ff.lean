/-!
# Pauli Anticommute
Category: Quantum Computing
Target: QC.pauli_anticommute
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The Pauli `X` matrix. -/
def sx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def sy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` matrix. -/
def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli matrices `X`, `Y`, `Z` pairwise anticommute and each squares to the
identity matrix. -/
theorem pauli_anticommute :
    sx * sy + sy * sx = 0 ∧ sy * sz + sz * sy = 0 ∧ sz * sx + sx * sz = 0 ∧
      sx * sx = 1 ∧ sy * sy = 1 ∧ sz * sz = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [sx, sy, sz, Matrix.mul_fin_two, Matrix.one_fin_two, ← Matrix.ext_iff,
      Fin.forall_fin_two, Complex.ext_iff] <;>
    norm_num [Complex.I_mul_I]

end QC

