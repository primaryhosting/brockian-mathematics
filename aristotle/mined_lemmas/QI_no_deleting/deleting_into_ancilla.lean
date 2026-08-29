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

lemma deleting_into_ancilla :
    ∃ U : Sys (Fin 2) ≃ₗᵢ[ℂ] Sys (Fin 2), ∀ u : EuclideanSpace ℂ (Fin 2),
      U (reg3 u u (qubit 1 0)) = reg3 u (qubit 1 0) u := by
  refine ⟨LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ swapLast, fun u => ?_⟩
  ext p
  obtain ⟨i, j, k⟩ := p
  simp [reg3, swapLast, LinearIsometryEquiv.piLpCongrLeft_apply]
  ring

end QI

