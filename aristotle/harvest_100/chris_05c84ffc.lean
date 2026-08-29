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
def Engine.Covers (E : Engine Req Eff) (r : Req) : Prop :=
  (E.recognize r).isSome

/-- One step of the engine, under the *bail on unrecognized* policy. -/
def Engine.step (E : Engine Req Eff) (r : Req) : Outcome Eff :=
  match E.recognize r with
  | some e => .perform e
  | none => .bail

/-- Executing a whole list of requests: the engine performs the effect of each
recognized request in turn and *halts* (bails) as soon as it meets a request
that its rule table does not cover. -/
def Engine.exec (E : Engine Req Eff) : List Req → List Eff
  | [] => []
  | r :: rs =>
      match E.recognize r with
      | some e => e :: E.exec rs
      | none => []

/-- The safety criterion on the rule table: every rule of the table produces a
safe effect for the requests it matches. -/
def Engine.RulesSafe (E : Engine Req Eff) (Safe : Req → Eff → Prop) : Prop :=
  ∀ r e, E.recognize r = some e → Safe r e

/-- Soundness of the engine: every effect it ever performs, on any input trace,
is attributable to a covered request in that trace and is safe for it. -/
def Engine.Sound (E : Engine Req Eff) (Safe : Req → Eff → Prop) : Prop :=
  ∀ rs : List Req, ∀ e ∈ E.exec rs, ∃ r ∈ rs, E.recognize r = some e ∧ Safe r e

/-! ### Basic characterisation of the bail policy -/

@[simp] theorem Engine.step_eq_bail_iff (E : Engine Req Eff) (r : Req) :
    E.step r = Outcome.bail ↔ ¬ E.Covers r := by
  unfold Engine.step Engine.Covers
  cases h : E.recognize r <;> simp

@[simp] theorem Engine.step_eq_perform_iff (E : Engine Req Eff) (r : Req) (e : Eff) :
    E.step r = Outcome.perform e ↔ E.recognize r = some e := by
  unfold Engine.step
  cases h : E.recognize r <;> simp

/-- Every effect appearing in an execution trace comes from a recognized request
of the input list. This is the *coverage* invariant of the bail policy. -/
theorem Engine.exec_mem_recognized (E : Engine Req Eff) :
    ∀ (rs : List Req) (e : Eff), e ∈ E.exec rs → ∃ r ∈ rs, E.recognize r = some e := by
  intro rs
  induction rs with
  | nil => intro e he; simp [Engine.exec] at he
  | cons r rs ih =>
      intro e he
      unfold Engine.exec at he
      cases h : E.recognize r with
      | none => rw [h] at he; simp at he
      | some e' =>
          rw [h] at he
          rcases List.mem_cons.mp he with he' | he'
          · exact ⟨r, List.mem_cons_self, by rw [h, he']⟩
          · obtain ⟨r', hr', hrec⟩ := ih e he'
            exact ⟨r', List.mem_cons_of_mem _ hr', hrec⟩

/-! ### Main theorem -/

/-- **Bailing on unrecognized requests is sound.**

If every rule of the isolation engine's table is safe, then the engine — which
performs an effect only for requests its table recognizes and otherwise halts —
never performs an unsafe effect, on any input trace.

Equivalently (contrapositive), any unsafe effect the engine can ever perform is
already witnessed by an unsafe rule in its table: unrecognized requests can
never be the source of unsoundness, precisely because the engine bails on them.
-/
theorem bail_on_unrecognized_is_sound
    (E : Engine Req Eff) (Safe : Req → Eff → Prop) (hrules : E.RulesSafe Safe) :
    E.Sound Safe := by
  intro rs e he
  obtain ⟨r, hr, hrec⟩ := E.exec_mem_recognized rs e he
  exact ⟨r, hr, hrec, hrules r e hrec⟩

/-- The contrapositive form of the main theorem: if the engine is unsound, the
blame lies with a rule of its table, never with an unrecognized request. -/
theorem unsound_imp_exists_unsafe_rule
    (E : Engine Req Eff) (Safe : Req → Eff → Prop) (h : ¬ E.Sound Safe) :
    ∃ r e, E.recognize r = some e ∧ ¬ Safe r e := by
  by_contra hc
  push_neg at hc
  exact h (bail_on_unrecognized_is_sound E Safe fun r e hre => hc r e hre)

/-- Conversely, the rule-safety criterion is also *necessary*: a sound engine
has a safe rule table (assuming every request may be submitted on its own).
Hence `RulesSafe` exactly characterises soundness. -/
theorem sound_iff_rulesSafe (E : Engine Req Eff) (Safe : Req → Eff → Prop) :
    E.Sound Safe ↔ E.RulesSafe Safe := by
  constructor
  · intro h r e hre
    have he : e ∈ E.exec [r] := by
      unfold Engine.exec; rw [hre]; simp [Engine.exec]
    obtain ⟨r', hr', _, hsafe⟩ := h [r] e he
    rw [List.mem_singleton] at hr'
    subst hr'
    exact hsafe
  · exact bail_on_unrecognized_is_sound E Safe

/-- The engine bails on exactly the requests outside its coverage; in
particular it performs no effect at all on an uncovered request. -/
theorem exec_of_not_covers (E : Engine Req Eff) (r : Req) (rs : List Req)
    (h : ¬ E.Covers r) : E.exec (r :: rs) = [] := by
  unfold Engine.Covers at h
  unfold Engine.exec
  cases hr : E.recognize r with
  | none => rfl
  | some e => rw [hr] at h; simp at h

end PCA.Coverage

