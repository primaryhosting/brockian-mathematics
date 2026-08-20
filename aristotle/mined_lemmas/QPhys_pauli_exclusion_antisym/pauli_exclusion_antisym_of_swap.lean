/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
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

namespace QPhys

variable {K H V : Type*} [Field K] [AddCommGroup H] [Module K H]
  [AddCommGroup V] [Module K V]

/-- The antisymmetrized (Slater-determinant) two-particle state built from the
single-particle states `psi` and `chi`, living in `H ⊗[K] H`. -/

theorem pauli_exclusion_antisym_of_swap [CharZero K] (Psi : H → H → V)
    (hPsi : ∀ psi chi, Psi chi psi = -Psi psi chi) (psi : H) : Psi psi psi = 0 := by
  have h : Psi psi psi = -Psi psi psi := hPsi psi psi
  have h2 : (2 : K) • Psi psi psi = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  simpa using h2

/-- Exterior-algebra form: the wedge square of a single-particle state vanishes,
`psi ∧ psi = 0`.  This is `ExteriorAlgebra.ι_sq_zero` in Mathlib. -/
