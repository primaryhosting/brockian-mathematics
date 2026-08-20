import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QI

/-- A single qubit: the two-dimensional complex Hilbert space `ℂ²`. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- Two qubits: the Hilbert space `ℂ² ⊗ ℂ² ≃ ℂ^(2×2)`. -/
abbrev TwoQubits : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor (Kronecker) product of two qubit states. -/

theorem no_deleting :
    ¬ ∃ (U : TwoQubits ≃ₗᵢ[ℂ] TwoQubits) (blank : Qubit),
        ∀ ψ : Qubit, ‖ψ‖ = 1 → U (kron ψ ψ) = kron ψ blank := by
  rintro ⟨U, blank, hU⟩
  exact no_deleting_isometry ⟨U.toLinearIsometry, blank, hU⟩

end QI

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

