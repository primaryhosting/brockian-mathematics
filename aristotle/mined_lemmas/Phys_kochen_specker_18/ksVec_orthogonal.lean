/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Phys

/-! ### The 18 vectors

We use the Cabello–Estebaranz–García-Alcaine 18-vector, 9-basis Kochen–Specker set in `ℝ⁴`.
The vectors have integer coordinates, listed here as rows. -/

/-- Integer coordinates of the 18 Kochen–Specker vectors. -/

lemma ksVec_orthogonal {i j : Fin 18} (h : ksDot i j = 0) :
    inner ℝ (ksVec i) (ksVec j) = 0 := by
  rw [inner_ksVec, h]
  simp

/-- All 18 vectors are nonzero, so four pairwise orthogonal ones really do form a basis of `ℝ⁴`. -/
