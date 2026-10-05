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

/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Coverage

open scoped Classical

universe u v

variable {I : Type u} {O : Type v}

/-- An *isolation engine*: a recognizer predicate carving out the inputs the engine
claims to cover, together with a total handler producing a candidate output. -/
structure Engine (I : Type u) (O : Type v) where
  /-- The inputs the engine claims to recognize (its coverage domain). -/
  recognizes : I → Prop
  /-- The candidate output produced on a recognized input. -/
  handle : I → O

/-- The engine's observable behaviour: answer on recognized inputs, **bail** (return `none`)
on everything else. -/

theorem sound_iff_coveredCorrect (E : Engine I O) (spec : I → O → Prop) :
    E.Sound spec ↔ E.CoveredCorrect spec :=
  ⟨coveredCorrect_of_sound E spec, bail_on_unrecognized_is_sound E spec⟩

/-- Completeness relative to the coverage domain: the engine answers on exactly the inputs
it recognizes. -/
