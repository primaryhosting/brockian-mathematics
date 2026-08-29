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

theorem density_matrix_unitary_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (U ρ : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (U * ρ * Uᴴ).PosSemidef ∧ (U * ρ * Uᴴ).trace = 1 := by
  refine ⟨posSemidef_conj U ρ hρ, ?_⟩
  have hU' : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hU).1
  rw [trace_conj_unitary U ρ hU', htr]

end QC

