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

lemma norm_qubit_minus : ‖qubit half (-half)‖ = 1 :=
  norm_qubit_of _ _ (by rw [norm_neg, norm_half_sq]; norm_num)

/-- `U` deletes the second copy of an unknown qubit: starting from `u ⊗ u ⊗ a` (two copies of an
arbitrary unknown qubit state `u`, together with a fixed ancilla state `a`) it produces
`u ⊗ b ⊗ a'`, where the "blank" state `b` and the final ancilla state `a'` do not depend on the
deleted state `u`. -/
