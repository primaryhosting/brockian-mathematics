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

/-! ## The model

An *isolation engine* is the runtime component of a proof-carrying app that stands
between an arbitrary input and a handler that has only been verified on a
recognized fragment of the input space.  The engine's policy is:

* if the input is *recognized*, run the handler on it;
* otherwise *bail* (refuse to act).

The soundness statement below says that this policy turns a handler which is
correct only on the recognized fragment into a total component that never
produces an unsafe outcome. -/

/-- The outcome of running the isolation engine on an input. -/
inductive Outcome (Output : Type v) : Type v
  | /-- The input was recognized and the handler produced `o`. -/
    handled (o : Output)
  | /-- The input was not recognized; the engine refused to act. -/
    bail
  deriving Repr, DecidableEq

/-- An isolation engine: a decidable recognizer for the fragment of the input
space that the handler is trusted on, together with the handler itself. -/
structure Engine (Input : Type u) (Output : Type v) where
  /-- Decision procedure recognizing the inputs the handler is verified for. -/
  recognized : Input → Bool
  /-- The (unverified on the whole domain) handler. -/
  handle : Input → Output

variable {Input : Type u} {Output : Type v}

/-- The bail-on-unrecognized policy. -/

theorem never_bails_of_total_coverage (E : Engine Input Output)
    (hcov : ∀ i : Input, E.recognized i = true) (i : Input) :
    E.run i ≠ Outcome.bail := by
  simp [hcov i]

/-- Under total coverage, soundness of the engine gives outright correctness of
the handler. -/
