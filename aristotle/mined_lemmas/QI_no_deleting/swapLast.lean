/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
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

namespace QI

/-- A qubit, i.e. a vector of the two-dimensional complex Hilbert space, given by its two
amplitudes. -/

def swapLast : (Fin 2 × Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2 × Fin 2) where
  toFun p := (p.1, p.2.2, p.2.1)
  invFun p := (p.1, p.2.2, p.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Sharpness of `QI.no_deleting`: the hypothesis that the final ancilla state does not depend on
the deleted state cannot be dropped. Swapping the second qubit register with the ancilla register
is a unitary that does turn `u ⊗ u ⊗ |0⟩` into `u ⊗ |0⟩ ⊗ u`, i.e. it erases the second copy of
`u`, but only at the price of moving it into the ancilla. -/
