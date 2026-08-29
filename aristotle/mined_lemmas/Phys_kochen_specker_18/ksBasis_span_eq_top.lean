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

theorem ksBasis_span_eq_top (j : Fin 9) :
    Submodule.span ℝ (Set.range fun k : Fin 4 => ksVecE (ksBasis j k)) = ⊤ :=
  (ksBasis_linearIndependent j).span_eq_top_of_card_eq_finrank (by
    simp [finrank_euclideanSpace])

/-- Every one of the 18 vectors occurs in exactly two of the 9 bases; consequently,
summing any weight function over all bases counts each vector twice. -/
