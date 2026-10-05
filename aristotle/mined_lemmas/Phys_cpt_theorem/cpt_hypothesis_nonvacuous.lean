/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Finset Matrix

/-- Complexified Minkowski space: four complex coordinates. -/
abbrev CMinkowski : Type := Fin 4 → ℂ

/-- The Minkowski metric signature `(+,-,-,-)`. -/

theorem cpt_hypothesis_nonvacuous :
    ∀ L : Matrix (Fin 4) (Fin 4) ℂ, ConnectedToIdentity L →
      ∀ x : Fin 1 → CMinkowski,
        (fun z : Fin 1 → CMinkowski => mform (z 0) (z 0)) (fun k => L.mulVec (x k)) =
          (fun z : Fin 1 → CMinkowski => mform (z 0) (z 0)) x := by
  rintro L ⟨p, -, -, hp1, hL⟩ x
  have : IsComplexLorentz L := hp1 ▸ hL 1
  exact this (x 0) (x 0)

#print axioms Phys.cpt_theorem

end Phys

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

