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
# A formal model of a "bail on unrecognized input" isolation engine

This file develops a small, self-contained formal model of the *isolation engine*
of a pattern-covering analyser (`PCA`), together with the soundness and
completeness statements of its `bail-on-unrecognized` policy.

## The model

* An `Engine` carries a finite (list) collection of recognized `patterns`, a
  matcher `applies : Pat → Req → Bool` telling which pattern applies to a
  request, and a `handler : Pat → Req → State → State` describing the effect of
  servicing a request through a given pattern.
* `dispatch` picks the first matching pattern, `Recognized r` says that some
  pattern in the engine's coverage applies `r`.
* `step` is the *fail-closed* one-step semantics: if a pattern applies, run its
  handler; otherwise **bail** (refuse to act) rather than guess.
* `run` iterates `step` over a trace of requests, stopping at the first bail.

## The guarantees

`PCA.Coverage.bail_on_unrecognized_is_sound` packages three facts, given only
that each individual handler preserves the isolation invariant `Inv` on the
requests it is allowed to service:

1. **Soundness (no escape).** Every state the engine can actually reach from an
   `Inv`-state satisfies `Inv`. No global coverage assumption is needed: the
   engine is safe on *arbitrary*, including adversarial, input.
2. **Completeness of the bail diagnosis (no spurious bails).** If the engine
   bails, this is witnessed by a genuinely unrecognized request in the trace.
3. **Liveness under coverage.** If every request in the trace is recognized,
   the engine never bails and terminates in a state satisfying `Inv`.
-/

namespace PCA
namespace Coverage

universe u v w

/-- The result of running the isolation engine: either a new state, or a
refusal to act (`bail`) because the input was not recognized. -/
inductive Outcome (State : Type u) where
  | ok : State → Outcome State
  | bail : Outcome State
  deriving Repr

/-- An isolation engine: a finite coverage of `patterns`, a matcher saying which
pattern applies to a request, and the state transformation performed when a
request is serviced through a pattern. -/
structure Engine (Pat : Type u) (Req : Type v) (State : Type w) where
  /-- The patterns the engine recognizes (its coverage). -/
  patterns : List Pat
  /-- `applies p r` says pattern `p` applies to request `r`. -/
  applies : Pat → Req → Bool
  /-- The state transformation performed when servicing `r` through `p`. -/
  handler : Pat → Req → State → State

namespace Engine

variable {Pat : Type u} {Req : Type v} {State : Type w}

/-- The pattern the engine selects for a request: the first one that applies. -/
def dispatch (E : Engine Pat Req State) (r : Req) : Option Pat :=
  E.patterns.find? (fun p => E.applies p r)

/-- A request is *recognized* when some pattern of the engine's coverage
applies it. -/
def Recognized (E : Engine Pat Req State) (r : Req) : Prop :=
  ∃ p ∈ E.patterns, E.applies p r = true

/-- One fail-closed step: service the request through its pattern if it is
recognized, otherwise refuse to act. -/
def step (E : Engine Pat Req State) (s : State) (r : Req) : Outcome State :=
  match E.dispatch r with
  | some p => Outcome.ok (E.handler p r s)
  | none => Outcome.bail

/-- Run the engine on a trace of requests, halting at the first bail. -/
def run (E : Engine Pat Req State) (s : State) : List Req → Outcome State
  | [] => Outcome.ok s
  | r :: rs =>
      match E.step s r with
      | Outcome.ok s' => E.run s' rs
      | Outcome.bail => Outcome.bail

/-- The obligation discharged for each individual pattern: its handler
preserves the isolation invariant on the requests it is allowed to service. -/
def HandlersSound (E : Engine Pat Req State) (Inv : State → Prop) : Prop :=
  ∀ p ∈ E.patterns, ∀ (r : Req) (s : State),
    E.applies p r = true → Inv s → Inv (E.handler p r s)

@[simp] theorem run_nil (E : Engine Pat Req State) (s : State) :
    E.run s [] = Outcome.ok s := rfl

theorem run_cons (E : Engine Pat Req State) (s : State) (r : Req) (rs : List Req) :
    E.run s (r :: rs) =
      match E.step s r with
      | Outcome.ok s' => E.run s' rs
      | Outcome.bail => Outcome.bail := rfl

/-- Dispatch fails exactly on unrecognized requests. -/
theorem dispatch_eq_none_iff (E : Engine Pat Req State) (r : Req) :
    E.dispatch r = none ↔ ¬ E.Recognized r := by
  constructor
  · intro h ⟨p, hp, hmp⟩
    have := List.find?_eq_none.mp h p hp
    exact this hmp
  · intro h
    refine List.find?_eq_none.mpr ?_
    intro p hp hmp
    exact h ⟨p, hp, hmp⟩

/-- A dispatched pattern belongs to the coverage and really applies. -/
theorem dispatch_spec (E : Engine Pat Req State) {r : Req} {p : Pat}
    (h : E.dispatch r = some p) : p ∈ E.patterns ∧ E.applies p r = true :=
  ⟨List.mem_of_find?_eq_some h, by
    have := List.find?_some h
    simpa using this⟩

/-- **One-step soundness.** A step from an invariant state either bails or lands
in an invariant state. -/
theorem step_sound {E : Engine Pat Req State} {Inv : State → Prop}
    (hH : E.HandlersSound Inv) {s : State} (hs : Inv s) (r : Req) {s' : State}
    (h : E.step s r = Outcome.ok s') : Inv s' := by
  unfold step at h
  cases hd : E.dispatch r with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some p =>
      rw [hd] at h
      obtain ⟨hp, hm⟩ := dispatch_spec E hd
      have : E.handler p r s = s' := by
        injection h
      subst this
      exact hH p hp r s hm hs

/-- A step bails exactly on an unrecognized request. -/
theorem step_bail_iff (E : Engine Pat Req State) (s : State) (r : Req) :
    E.step s r = Outcome.bail ↔ ¬ E.Recognized r := by
  rw [← dispatch_eq_none_iff]
  unfold step
  cases hd : E.dispatch r with
  | none => simp
  | some p => simp

/-- A recognized request produces a successful step. -/
theorem step_ok_of_recognized (E : Engine Pat Req State) (s : State) {r : Req}
    (h : E.Recognized r) : ∃ s', E.step s r = Outcome.ok s' := by
  unfold step
  cases hd : E.dispatch r with
  | none => exact absurd ((dispatch_eq_none_iff E r).mp hd) (by simpa using h)
  | some p => exact ⟨E.handler p r s, by simp⟩

/-- **Soundness of the whole run.** Any state reachable from an invariant state
satisfies the invariant, for an arbitrary (possibly adversarial) trace. -/
theorem run_sound {E : Engine Pat Req State} {Inv : State → Prop}
    (hH : E.HandlersSound Inv) :
    ∀ (rs : List Req) (s : State), Inv s → ∀ s', E.run s rs = Outcome.ok s' → Inv s' := by
  intro rs
  induction rs with
  | nil =>
      intro s hs s' h
      rw [run_nil] at h
      have : s = s' := by injection h
      exact this ▸ hs
  | cons r rs ih =>
      intro s hs s' h
      rw [run_cons] at h
      cases hstep : E.step s r with
      | bail => rw [hstep] at h; exact absurd h (by simp)
      | ok t =>
          rw [hstep] at h
          exact ih t (step_sound hH hs r hstep) s' h

/-- **Completeness of the bail diagnosis.** If the engine bails on a trace, some
request in that trace is genuinely unrecognized. -/
theorem run_bail_witness (E : Engine Pat Req State) :
    ∀ (rs : List Req) (s : State), E.run s rs = Outcome.bail →
      ∃ r ∈ rs, ¬ E.Recognized r := by
  intro rs
  induction rs with
  | nil => intro s h; exact absurd h (by simp)
  | cons r rs ih =>
      intro s h
      rw [run_cons] at h
      cases hstep : E.step s r with
      | bail =>
          exact ⟨r, List.mem_cons_self .., (step_bail_iff E s r).mp hstep⟩
      | ok t =>
          rw [hstep] at h
          obtain ⟨r', hr', hnr'⟩ := ih t h
          exact ⟨r', List.mem_cons_of_mem _ hr', hnr'⟩

/-- **Liveness under coverage.** On a fully recognized trace the engine never
bails. -/
theorem run_ok_of_covered (E : Engine Pat Req State) :
    ∀ (rs : List Req) (s : State), (∀ r ∈ rs, E.Recognized r) →
      ∃ s', E.run s rs = Outcome.ok s' := by
  intro rs
  induction rs with
  | nil => intro s _; exact ⟨s, rfl⟩
  | cons r rs ih =>
      intro s hcov
      obtain ⟨t, ht⟩ := step_ok_of_recognized E s (hcov r (List.mem_cons_self ..))
      obtain ⟨s', hs'⟩ := ih t (fun x hx => hcov x (List.mem_cons_of_mem _ hx))
      exact ⟨s', by rw [run_cons, ht]; exact hs'⟩

end Engine

/--
**Soundness and completeness of the isolation engine's `bail-on-unrecognized`
policy.**

Assume only that each pattern's handler preserves the isolation invariant `Inv`
on the requests it is allowed to service (`HandlersSound`). Then, starting from
any state satisfying `Inv`, and for an *arbitrary* trace of requests:

1. *Soundness (no escape).* every state the engine can reach satisfies `Inv`;
2. *Completeness of the bail diagnosis (no spurious bails).* if the engine
   bails, some request in the trace really is outside the engine's coverage;
3. *Liveness under coverage.* if the whole trace is covered by the engine's
   patterns, the engine completes without bailing, in a state satisfying `Inv`.

In particular the isolation guarantee (1) needs no coverage assumption
whatsoever: refusing to act on unrecognized input is what makes the engine sound
against inputs its pattern set never anticipated.
-/
theorem bail_on_unrecognized_is_sound
    {Pat : Type u} {Req : Type v} {State : Type w}
    (E : Engine Pat Req State) (Inv : State → Prop)
    (hH : E.HandlersSound Inv) (s : State) (hs : Inv s) (rs : List Req) :
    (∀ s', E.run s rs = Outcome.ok s' → Inv s') ∧
    (E.run s rs = Outcome.bail → ∃ r ∈ rs, ¬ E.Recognized r) ∧
    ((∀ r ∈ rs, E.Recognized r) → ∃ s', E.run s rs = Outcome.ok s' ∧ Inv s') := by
  refine ⟨Engine.run_sound hH rs s hs, Engine.run_bail_witness E rs s, ?_⟩
  intro hcov
  obtain ⟨s', hs'⟩ := Engine.run_ok_of_covered E rs s hcov
  exact ⟨s', hs', Engine.run_sound hH rs s hs s' hs'⟩

/-! ### Non-vacuity

A concrete engine showing that the model is inhabited, that bails really can
happen, and that the invariant is a genuine constraint: states are the sets of
capabilities currently exposed by the sandbox, the invariant is that the exposure
stays inside the sandbox budget `{0, 1}`, and the two recognized patterns only
ever expose capability `0` or capability `1`.
-/

/-- A concrete two-pattern engine over natural-number capabilities. -/
def demoEngine : Engine ℕ ℕ (Finset ℕ) where
  patterns := [0, 1]
  applies p r := decide (p = r)
  handler p _ s := insert p s

/-- The demo engine's isolation invariant: exposure stays within the budget. -/
def demoInv (s : Finset ℕ) : Prop := s ⊆ ({0, 1} : Finset ℕ)

theorem demoEngine_handlers_sound : demoEngine.HandlersSound demoInv := by
  intro p hp r s _ hs
  have hp' : p = 0 ∨ p = 1 := by
    simpa [demoEngine] using hp
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · rcases hp' with rfl | rfl <;> simp
  · exact hs hx

/-- The engine really does bail on an input outside its coverage. -/
theorem demoEngine_bails : demoEngine.run ∅ [0, 2, 1] = Outcome.bail := by
  rfl

/-- On a covered trace it completes, and the reached state respects the budget. -/
theorem demoEngine_runs :
    demoEngine.run ∅ [0, 1] = Outcome.ok {1, 0} := by
  rfl

theorem demoEngine_reachable_inv (rs : List ℕ) (s' : Finset ℕ)
    (h : demoEngine.run ∅ rs = Outcome.ok s') : demoInv s' :=
  (bail_on_unrecognized_is_sound demoEngine demoInv demoEngine_handlers_sound ∅
    (by simp [demoInv]) rs).1 s' h

end Coverage
end PCA

