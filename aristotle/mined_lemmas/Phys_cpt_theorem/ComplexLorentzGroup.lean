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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- Complexified Minkowski spacetime: four complex coordinates. -/
abbrev Spacetime : Type := Fin 4 → ℂ

/-- The Minkowski metric `diag (1, -1, -1, -1)`, complexified. -/

def ComplexLorentzGroup : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
  {L | IsComplexLorentz L}

/-- The total spacetime inversion `x ↦ -x` (the `PT` part of `CPT`). -/
