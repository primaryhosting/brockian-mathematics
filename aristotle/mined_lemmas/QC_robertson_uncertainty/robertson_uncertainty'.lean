import Mathlib
/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
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

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator `A` is *symmetric* (a quantum observable) when
`⟪A x, y⟫ = ⟪x, A y⟫` for all `x, y`.  On a complete space this is exactly
self-adjointness. -/

theorem robertson_uncertainty' (A B : E →L[ℂ] E) (hA : IsObservable A) (hB : IsObservable B)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    Delta A ψ * Delta B ψ ≥ (1 / 2 : ℝ) * ‖expect (comm A B) ψ‖ := by
  have := robertson_uncertainty A B hA hB ψ hψ
  linarith

end QC

#print axioms QC.robertson_uncertainty
#print axioms QC.robertson_uncertainty'

