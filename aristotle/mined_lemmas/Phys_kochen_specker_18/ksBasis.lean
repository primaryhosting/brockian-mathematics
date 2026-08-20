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

def ksBasis : Fin 9 → Finset (Fin 18) :=
  ![{0, 1, 2, 3},
    {0, 4, 5, 6},
    {7, 8, 2, 9},
    {7, 10, 6, 11},
    {1, 4, 12, 13},
    {8, 10, 13, 14},
    {15, 16, 3, 9},
    {15, 17, 5, 11},
    {16, 17, 12, 14}]

