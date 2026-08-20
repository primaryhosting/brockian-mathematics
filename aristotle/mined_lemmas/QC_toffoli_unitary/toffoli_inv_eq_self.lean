/-
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix
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

/-- The permutation of the computational basis `{|abc⟩}` (indexed by `4a + 2b + c`)
implemented by the Toffoli (CCNOT) gate: it exchanges `|110⟩` and `|111⟩` and fixes
all other basis states. -/

theorem toffoli_inv_eq_self :
    (⟨toffoli, toffoli_unitary⟩ : Matrix.unitaryGroup (Fin 8) ℂ)⁻¹
      = ⟨toffoli, toffoli_unitary⟩ := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j
  simpa using congrFun (congrFun toffoli_mul_self i) j

end QC

