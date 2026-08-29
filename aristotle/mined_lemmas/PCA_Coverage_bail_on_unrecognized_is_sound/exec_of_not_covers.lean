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

import Mathlib

set_option autoImplicit false

namespace PCA.Coverage

universe u v

/-- The outcome of feeding a single request to the isolation engine: either the
engine recognized the request and performed the corresponding effect, or it did
not recognize it and bailed out. -/
inductive Outcome (Eff : Type v) where
  | bail : Outcome Eff
  | perform : Eff → Outcome Eff
  deriving DecidableEq

/-- An isolation engine is given by a partial recognizer: a request is either
matched by some rule of the engine's table, yielding the effect that the engine
would perform, or it is unmatched (`none`). -/
structure Engine (Req : Type u) (Eff : Type v) where
  /-- Partial recognizer / rule table of the engine. -/
  recognize : Req → Option Eff

variable {Req : Type u} {Eff : Type v}

/-- The set of requests the engine's rule table covers. -/

theorem exec_of_not_covers (E : Engine Req Eff) (r : Req) (rs : List Req)
    (h : ¬ E.Covers r) : E.exec (r :: rs) = [] := by
  unfold Engine.Covers at h
  unfold Engine.exec
  cases hr : E.recognize r with
  | none => rfl
  | some e => rw [hr] at h; simp at h

end PCA.Coverage

