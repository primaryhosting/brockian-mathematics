/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
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

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Complexified Minkowski space `ℂ⁴`. -/
abbrev CVec : Type := Fin 4 → ℂ

/-- The (bilinear, not sesquilinear) Minkowski form of signature `(+,-,-,-)` on complexified
Minkowski space. -/

lemma ptPath_zero : ptPath 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ptPath]

