/-
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix
open scoped ComplexOrder

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

namespace QC

/-- Conjugating a positive semidefinite matrix by any matrix keeps it
positive semidefinite: `U ρ U†  ⪰ 0`. -/

theorem posSemidef_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    (U * ρ * Uᴴ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same U

/-- The trace is invariant under unitary conjugation:
`Tr (U ρ U†) = Tr ρ` whenever `U† U = 1`. -/
