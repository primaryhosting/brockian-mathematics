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

theorem unsound_imp_exists_unsafe_rule
    (E : Engine Req Eff) (Safe : Req → Eff → Prop) (h : ¬ E.Sound Safe) :
    ∃ r e, E.recognize r = some e ∧ ¬ Safe r e := by
  by_contra hc
  push_neg at hc
  exact h (bail_on_unrecognized_is_sound E Safe fun r e hre => hc r e hre)

/-- Conversely, the rule-safety criterion is also *necessary*: a sound engine
has a safe rule table (assuming every request may be submitted on its own).
Hence `RulesSafe` exactly characterises soundness. -/
