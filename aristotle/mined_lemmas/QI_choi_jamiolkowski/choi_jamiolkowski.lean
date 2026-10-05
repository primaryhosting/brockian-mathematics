import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ → Mₘ`, indexed by `(n × m) × (n × m)`:
`C (i,a) (j,b) = (Φ (Eᵢⱼ)) a b`. -/

theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef) ∧
      (IsCompletelyPositive Φ ↔ HasKrausRepresentation Φ) := by
  have h1 : IsCompletelyPositive Φ → (choiMatrix Φ).PosSemidef :=
    choiMatrix_posSemidef_of_completelyPositive
  have h2 : (choiMatrix Φ).PosSemidef → HasKrausRepresentation Φ :=
    hasKrausRepresentation_of_choiMatrix_posSemidef
  have h3 : HasKrausRepresentation Φ → IsCompletelyPositive Φ :=
    isCompletelyPositive_of_kraus
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨fun h => h2 (h1 h), h3⟩⟩

end QI

#print axioms QI.choi_jamiolkowski

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

