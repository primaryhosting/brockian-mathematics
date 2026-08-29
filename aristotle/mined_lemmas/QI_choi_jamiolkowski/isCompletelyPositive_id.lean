/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` lines to
-- precede any module docstring; the same text is repeated verbatim below.)
import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ(ℂ) →ₗ Mₘ(ℂ)`:
`C (i,k) (j,l) = (Φ Eᵢⱼ) k l`, where the `Eᵢⱼ` are the matrix units. -/

theorem isCompletelyPositive_id :
    IsCompletelyPositive (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :=
  isCompletelyPositive_of_hasKrausDecomposition _ ⟨1, fun _ => 1, by intro X; simp⟩

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

