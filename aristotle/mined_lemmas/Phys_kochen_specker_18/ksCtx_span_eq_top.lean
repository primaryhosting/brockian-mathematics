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

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/

theorem ksCtx_span_eq_top (c : Fin 9) :
    Submodule.span ℝ (Set.range fun i : Fin 4 => ksVec (ksCtx c i)) = ⊤ := by
  have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) := by simp
  have hb := (basisOfLinearIndependentOfCardEqFinrank (ksCtx_linearIndependent c) hcard).span_eq
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at hb

/-- **Kochen–Specker (18-vector version).**  There is no `{0,1}`-coloring of `ℝ⁴`
assigning to each of the nine orthogonal bases listed in `Phys.ksCtx` exactly one
vector of color `1`. -/
