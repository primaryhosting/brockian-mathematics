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

theorem pbr_orthogonal_to_prep (x : Fin 2 × Fin 2) :
    inner2 (pbrVec x) (tensor (qstate x.1) (qstate x.2)) = 0 := by
  obtain ⟨x1, x2⟩ := x
  fin_cases x1 <;> fin_cases x2 <;>
    (simp [inner2_eq, pbrVec, tensor, qstate, ket0, ket1, ketPlus, ketMinus, conj_invSqrtTwo]
      <;> try ring)

/-! ## Measure-theoretic preliminaries -/

/-- Monotonicity of the product of measures. -/
