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

lemma ksVecZ_injective : Function.Injective ksVecZ := by decide

/-- **No `{0,1}`-coloring**: there is no assignment of values in `{0,1}` to the 18 vectors
such that exactly one vector of each of the nine orthogonal bases receives the value `1`. -/
