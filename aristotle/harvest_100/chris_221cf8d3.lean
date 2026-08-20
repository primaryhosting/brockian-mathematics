/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/- This development is self-contained: it needs nothing beyond Lean core, so the
file has no `import` line (a module doc comment must precede any import). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Coverage

universe u v

/-- The result the isolation engine may return: either it performs an action it
recognized as safe, or it *bails out* (refuses to act). -/
inductive Outcome (Action : Type v) : Type v
  | act : Action → Outcome Action
  | bail : Outcome Action
  deriving DecidableEq

/-- A model of the isolation engine.

* `recognize` is the (partial) recognizer: it returns the action to perform on
  inputs it understands, and `none` on inputs outside its coverage.
* `safe i a` is the specification: performing `a` on input `i` is safe.
* `recognized_is_safe` is the *proof carried by the app*: whenever the engine
  claims to recognize an input, the action it proposes meets the specification.

Note that nothing is assumed about the behaviour of `safe` on unrecognized
inputs; coverage of the recognizer is deliberately left partial. -/
structure Engine (Input : Type u) (Action : Type v) where
  recognize : Input → Option Action
  safe : Input → Action → Prop
  recognized_is_safe : ∀ i a, recognize i = some a → safe i a

variable {Input : Type u} {Action : Type v}

/-- The engine's dispatch loop: act on recognized inputs, bail on everything else. -/
def Engine.run (E : Engine Input Action) (i : Input) : Outcome Action :=
  match E.recognize i with
  | some a => Outcome.act a
  | none => Outcome.bail

/-- What it means for an outcome to be acceptable on input `i`: an action must be
safe, while bailing out is always acceptable. -/
def Engine.OutcomeOK (E : Engine Input Action) (i : Input) : Outcome Action → Prop
  | Outcome.act a => E.safe i a
  | Outcome.bail => True

@[simp] theorem Engine.OutcomeOK_act (E : Engine Input Action) (i : Input) (a : Action) :
    E.OutcomeOK i (Outcome.act a) ↔ E.safe i a := Iff.rfl

@[simp] theorem Engine.OutcomeOK_bail (E : Engine Input Action) (i : Input) :
    E.OutcomeOK i Outcome.bail := trivial

@[simp] theorem Engine.run_eq_act_iff (E : Engine Input Action) (i : Input) (a : Action) :
    E.run i = Outcome.act a ↔ E.recognize i = some a := by
  unfold Engine.run
  cases h : E.recognize i with
  | none => simp
  | some b => simp [Outcome.act.injEq]

@[simp] theorem Engine.run_eq_bail_iff (E : Engine Input Action) (i : Input) :
    E.run i = Outcome.bail ↔ E.recognize i = none := by
  unfold Engine.run
  cases h : E.recognize i with
  | none => simp
  | some b => simp

/-- **Bailing out on unrecognized input is sound.**

For every engine and every input, the three defining guarantees of the
"bail on unrecognized" dispatch strategy hold simultaneously:

1. *Soundness*: the outcome produced by the engine always meets the
   specification — any action actually taken is safe.
2. *Isolation*: the engine acts only on inputs it recognizes; on an input
   outside its coverage it bails out and does nothing.
3. *Completeness relative to coverage*: on every recognized input the engine
   does act, with exactly the recognized action — bailing out is never used as
   an escape hatch on inputs inside the coverage.
-/
theorem bail_on_unrecognized_is_sound (E : Engine Input Action) (i : Input) :
    E.OutcomeOK i (E.run i) ∧
      (E.recognize i = none → E.run i = Outcome.bail) ∧
      (∀ a : Action, E.recognize i = some a → E.run i = Outcome.act a) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Engine.run
    cases h : E.recognize i with
    | none => simp [Engine.OutcomeOK]
    | some a => simpa [Engine.OutcomeOK] using E.recognized_is_safe i a h
  · intro h; simpa using h
  · intro a h; simpa using h

/-- Corollary: the engine never performs an unsafe action. -/
theorem act_is_safe (E : Engine Input Action) (i : Input) (a : Action)
    (h : E.run i = Outcome.act a) : E.safe i a := by
  have := (bail_on_unrecognized_is_sound E i).1
  rw [h] at this
  exact this

/-- Corollary: if an outcome other than `bail` is produced, the input was recognized. -/
theorem acts_only_on_recognized (E : Engine Input Action) (i : Input)
    (h : E.run i ≠ Outcome.bail) : ∃ a : Action, E.recognize i = some a := by
  cases hr : E.recognize i with
  | none => exact absurd ((E.run_eq_bail_iff i).2 hr) h
  | some a => exact ⟨a, rfl⟩

end PCA.Coverage

