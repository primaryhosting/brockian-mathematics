/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
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

namespace Frontier

/-- An explicit vector of the real Hilbert space `ℝ⁴`. -/

def IsKSValuation (f : EuclideanSpace ℝ (Fin 4) → Prop) : Prop :=
  ∀ v : Fin 4 → EuclideanSpace ℝ (Fin 4), (∀ i, v i ≠ 0) →
    (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) → ∃! i, f (v i)

/-- The `{0,1}` indicator of a proposition. -/
