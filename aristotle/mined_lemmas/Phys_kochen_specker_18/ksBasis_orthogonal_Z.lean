import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
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

namespace Phys

/-- Integer coordinates of the 18 vectors of the Cabello–Estebaranz–García-Alcaine
Kochen–Specker set in `ℝ⁴`. -/

lemma ksBasis_orthogonal_Z (j : Fin 9) :
    ∀ i ∈ ksBasis j, ∀ i' ∈ ksBasis j, i ≠ i' → ∑ k : Fin 4, ksVecZ i k * ksVecZ i' k = 0 := by
  fin_cases j <;> decide

/-- Each index lies in exactly two of the nine sets. -/
