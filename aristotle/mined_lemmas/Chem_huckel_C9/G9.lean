import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
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

namespace Chem

open Complex Matrix Polynomial

/-- A primitive ninth root of unity. -/

noncomputable def G9 : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.of fun k j => (9 : ℂ)⁻¹ * (om ^ (k.val * j.val))⁻¹

