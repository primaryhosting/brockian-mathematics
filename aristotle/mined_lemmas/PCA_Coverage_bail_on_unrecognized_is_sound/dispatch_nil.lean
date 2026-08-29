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
set_option relaxedAutoImplicit false

namespace PCA.Coverage

universe u v

/-- A single handling *rule* of the isolation engine: a decidable guard saying which
inputs the rule recognizes, together with the action it performs on such inputs. -/
structure Rule (Input : Type u) (Output : Type v) where
  /-- The guard: `guard i = true` means this rule recognizes the input `i`. -/
  guard : Input → Bool
  /-- The action performed on a recognized input. -/
  action : Input → Output

variable {Input : Type u} {Output : Type v}

/-- A rule is *sound* for a specification `spec` when, on every input it recognizes,
its action satisfies the specification. Nothing at all is required of the action off
the guard — that is the point of isolating unrecognized inputs. -/

@[simp] theorem dispatch_nil (i : Input) : dispatch ([] : List (Rule Input Output)) i = none :=
  rfl

