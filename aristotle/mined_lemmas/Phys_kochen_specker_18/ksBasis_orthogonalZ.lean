/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
recorded with integer entries. -/

theorem ksBasis_orthogonalZ (j : Fin 9) (k l : Fin 4) (h : k ≠ l) :
    ∑ m : Fin 4, ksVecZ (ksBasis j k) m * ksVecZ (ksBasis j l) m = 0 := by
  revert j k l; decide

/-- Each of the 9 quadruples consists of pairwise orthogonal vectors of `ℝ⁴`. -/
