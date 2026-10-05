import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

set_option grind.warning false

open MeasureTheory

noncomputable section

namespace QI

/-! ## The quantum ingredients

We work with a single qubit modelled as `Fin 2 → ℂ` and a pair of qubits modelled as
`Fin 2 × Fin 2 → ℂ` (the tensor product `ℂ² ⊗ ℂ²`), equipped with the standard Hermitian
inner product `inner2`.
-/

/-- The scalar `1/√2`. -/

lemma inner2_eq (u v : Fin 2 × Fin 2 → ℂ) :
    inner2 u v = (starRingEnd ℂ) (u (0, 0)) * v (0, 0) + (starRingEnd ℂ) (u (0, 1)) * v (0, 1)
      + (starRingEnd ℂ) (u (1, 0)) * v (1, 0) + (starRingEnd ℂ) (u (1, 1)) * v (1, 1) := by
  simp [inner2, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

/-- The PBR vectors form an orthonormal basis of `ℂ² ⊗ ℂ²`, i.e. they really do describe a
projective measurement on the two-qubit system. -/
