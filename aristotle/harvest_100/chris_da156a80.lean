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
def Engine.run (E : Engine Input Output) (i : Input) : Outcome Output :=
  if E.recognized i then Outcome.handled (E.handle i) else Outcome.bail

/-- An outcome is safe for input `i` w.r.t. the safety relation `safe` when either
it is a handled output satisfying `safe`, or the engine bailed (refusing to act
is always safe). -/
def Outcome.SafeFor (safe : Input → Output → Prop) (i : Input) :
    Outcome Output → Prop
  | Outcome.handled o => safe i o
  | Outcome.bail => True

@[simp] theorem Outcome.safeFor_handled (safe : Input → Output → Prop) (i : Input)
    (o : Output) : (Outcome.handled o).SafeFor safe i ↔ safe i o := Iff.rfl

@[simp] theorem Outcome.safeFor_bail (safe : Input → Output → Prop) (i : Input) :
    (Outcome.bail : Outcome Output).SafeFor safe i := trivial

@[simp] theorem Engine.run_of_recognized (E : Engine Input Output) {i : Input}
    (h : E.recognized i = true) : E.run i = Outcome.handled (E.handle i) := by
  -- `if_pos` from core closes this once the condition is discharged.
  simp [Engine.run, h]

@[simp] theorem Engine.run_of_unrecognized (E : Engine Input Output) {i : Input}
    (h : E.recognized i = false) : E.run i = Outcome.bail := by
  -- `if_neg` from core closes this once the condition is discharged.
  simp [Engine.run, h]

/-! ## Soundness -/

/-- **Bail on unrecognized is sound.**

If a handler is correct (produces a `safe` output) on every input its recognizer
accepts, then the isolation engine that bails on unrecognized inputs produces a
safe outcome on *every* input, recognized or not. -/
theorem bail_on_unrecognized_is_sound
    (E : Engine Input Output) (safe : Input → Output → Prop)
    (hhandler : ∀ i : Input, E.recognized i = true → safe i (E.handle i)) :
    ∀ i : Input, (E.run i).SafeFor safe i := by
  intro i
  cases hi : E.recognized i with
  | false => simp [E.run_of_unrecognized hi]
  | true => simpa [E.run_of_recognized hi] using hhandler i hi

/-! ## Sharpness and completeness of the policy -/

/-- The engine bails exactly on the unrecognized inputs: the policy is not
over-conservative. -/
theorem run_eq_bail_iff (E : Engine Input Output) (i : Input) :
    E.run i = Outcome.bail ↔ E.recognized i = false := by
  cases hi : E.recognized i with
  | false => simp [hi]
  | true => simp [hi]

/-- Whenever the engine does act, it acts by running the handler on a recognized
input. -/
theorem run_eq_handled_iff (E : Engine Input Output) (i : Input) (o : Output) :
    E.run i = Outcome.handled o ↔ E.recognized i = true ∧ o = E.handle i := by
  cases hi : E.recognized i with
  | false => simp [hi]
  | true => simp [hi, eq_comm]

/-- **Coverage.** If the recognizer accepts the whole input space, the engine
never bails: soundness is then bought at no cost in functionality. -/
theorem never_bails_of_total_coverage (E : Engine Input Output)
    (hcov : ∀ i : Input, E.recognized i = true) (i : Input) :
    E.run i ≠ Outcome.bail := by
  simp [hcov i]

/-- Under total coverage, soundness of the engine gives outright correctness of
the handler. -/
theorem handler_safe_of_total_coverage (E : Engine Input Output)
    (safe : Input → Output → Prop) (hcov : ∀ i : Input, E.recognized i = true)
    (hsound : ∀ i : Input, (E.run i).SafeFor safe i) (i : Input) :
    safe i (E.handle i) := by
  simpa [E.run_of_recognized (hcov i)] using hsound i

/-- The handler-correctness hypothesis of `bail_on_unrecognized_is_sound` is
necessary: an engine that recognizes an input on which the handler is unsafe is
not sound. -/
theorem not_sound_of_unsafe_recognized (E : Engine Input Output)
    (safe : Input → Output → Prop) (i : Input) (hi : E.recognized i = true)
    (hbad : ¬ safe i (E.handle i)) :
    ¬ (∀ j : Input, (E.run j).SafeFor safe j) := by
  intro hsound
  exact hbad (by simpa [E.run_of_recognized hi] using hsound i)

end PCA.Coverage

#print axioms PCA.Coverage.bail_on_unrecognized_is_sound

