import Mathlib

/-!
# A formal model of an isolation engine, with soundness and completeness

This file develops a small, self-contained transition-system model of an *isolation
engine* (`PCA.Isolation.Engine`) together with the notion of a machine-checkable
*isolation certificate* (`PCA.Isolation.Certificate`).

The engine is an abstract nondeterministic transition system with

* a set of initial states,
* an action-labelled step relation,
* a `breach` predicate marking the states that violate isolation
  (e.g. a compartment boundary has been crossed),

and an *escape* is a reachable breach state.

A certificate is an inductive-invariant style proof object.  Crucially, a certificate
is allowed to declare a set of `trusted` actions whose transitions it did **not**
verify; a certificate is `Clean` when that set is empty.

The main results are:

* `PCA.Isolation.no_clean_proved_with_escape` (soundness): no engine simultaneously
  admits a clean certificate and an escape.
* `PCA.Isolation.exists_clean_certificate_of_not_escape` (completeness): every
  escape-free engine admits a clean certificate.
* `PCA.Isolation.clean_certificate_iff_not_escape`: the two notions coincide.
* `PCA.Isolation.exists_engine_certificate_escape`: cleanliness cannot be dropped —
  there is an engine with a (non-clean) certificate that nonetheless escapes.
* `PCA.Isolation.escape_iff_exists_witness`: escapes are always witnessed by a finite
  execution trace, so the model is refutation-complete as well.
-/

set_option autoImplicit false

namespace PCA
namespace Isolation

universe u v

/-- An isolation engine: an action-labelled nondeterministic transition system on a
state space `S`, together with a predicate singling out the states that breach
isolation. -/
structure Engine (S : Type u) (A : Type v) where
  /-- The initial (boot) states of the engine. -/
  init : S → Prop
  /-- The step relation: `step s a s'` means action `a` can take state `s` to `s'`. -/
  step : S → A → S → Prop
  /-- The states in which the isolation guarantee is violated. -/
  breach : S → Prop

variable {S : Type u} {A : Type v}

/-- States reachable from an initial state by finitely many steps. -/
inductive Reachable (e : Engine S A) : S → Prop
  | init {s : S} : e.init s → Reachable e s
  | step {s : S} {a : A} {s' : S} : Reachable e s → e.step s a s' → Reachable e s'

/-- An *escape*: some reachable state breaches isolation. -/
def Escape (e : Engine S A) : Prop := ∃ s : S, Reachable e s ∧ e.breach s

/-- An isolation certificate for `e`: an invariant `inv` that holds initially, is
preserved by every step whose action is not `trusted`, and excludes all breach states.

The `trusted` field records the actions the certificate did *not* check; a certificate
with a nonempty trusted set is only as good as the assumptions it makes. -/
structure Certificate (e : Engine S A) where
  /-- The candidate invariant. -/
  inv : S → Prop
  /-- Actions whose transitions the certificate leaves unverified (assumed benign). -/
  trusted : A → Prop
  /-- The invariant covers all initial states. -/
  init_holds : ∀ s : S, e.init s → inv s
  /-- The invariant is preserved by every verified step. -/
  step_preserves : ∀ (s : S) (a : A) (s' : S), ¬ trusted a → inv s → e.step s a s' → inv s'
  /-- The invariant rules out breaches. -/
  excludes_breach : ∀ s : S, inv s → ¬ e.breach s

/-- A certificate is *clean* when it trusts no action, i.e. it verifies every
transition of the engine. -/
def Certificate.Clean {e : Engine S A} (c : Certificate e) : Prop := ∀ a : A, ¬ c.trusted a

/-- The engine is *proved* (with a clean certificate) when such a certificate exists. -/
def Proved (e : Engine S A) : Prop := ∃ c : Certificate e, c.Clean

/-- A clean certificate's invariant holds at every reachable state. -/
theorem Certificate.inv_of_reachable {e : Engine S A} (c : Certificate e) (hc : c.Clean)
    {s : S} (hs : Reachable e s) : c.inv s := by
  induction hs with
  | init h => exact c.init_holds _ h
  | step _ hstep ih => exact c.step_preserves _ _ _ (hc _) ih hstep

/-- **Soundness.** No isolation engine admits both a clean certificate and an escape. -/
theorem no_clean_proved_with_escape (e : Engine S A) :
    ¬ ∃ c : Certificate e, c.Clean ∧ Escape e := by
  rintro ⟨c, hc, s, hreach, hbreach⟩
  exact c.excludes_breach s (c.inv_of_reachable hc hreach) hbreach

/-- Soundness, phrased with `Proved`. -/
theorem not_escape_of_proved {e : Engine S A} (h : Proved e) : ¬ Escape e := by
  rintro hesc
  obtain ⟨c, hc⟩ := h
  exact no_clean_proved_with_escape e ⟨c, hc, hesc⟩

/-- The canonical certificate of an escape-free engine: reachability itself. -/
def reachabilityCertificate (e : Engine S A) (h : ¬ Escape e) : Certificate e where
  inv := Reachable e
  trusted := fun _ => False
  init_holds := fun _ hs => Reachable.init hs
  step_preserves := fun _ _ _ _ hs hstep => Reachable.step hs hstep
  excludes_breach := fun s hs hb => h ⟨s, hs, hb⟩

theorem reachabilityCertificate_clean (e : Engine S A) (h : ¬ Escape e) :
    (reachabilityCertificate e h).Clean := fun _ hb => hb

/-- **Completeness.** Every escape-free engine admits a clean certificate. -/
theorem exists_clean_certificate_of_not_escape (e : Engine S A) (h : ¬ Escape e) :
    ∃ c : Certificate e, c.Clean :=
  ⟨reachabilityCertificate e h, reachabilityCertificate_clean e h⟩

/-- Soundness and completeness combined: an engine is escape-free exactly when it has a
clean certificate. -/
theorem clean_certificate_iff_not_escape (e : Engine S A) :
    Proved e ↔ ¬ Escape e :=
  ⟨not_escape_of_proved, exists_clean_certificate_of_not_escape e⟩

/-!
### Cleanliness is necessary

Dropping the `Clean` hypothesis makes the soundness statement false: a certificate that
trusts an action can coexist with an escape performed by exactly that action.
-/

/-- A two-state engine: the initial state `false` steps, via the single action `()`,
to the breach state `true`.  The certificate below trusts that action. -/
def escapeEngine : Engine Bool Unit where
  init := fun s => s = false
  step := fun s _ s' => s = false ∧ s' = true
  breach := fun s => s = true

/-- A certificate for `escapeEngine` which is *not* clean: it trusts the only action. -/
def escapeCertificate : Certificate escapeEngine where
  inv := fun s => s = false
  trusted := fun _ => True
  init_holds := fun _ h => h
  step_preserves := fun _ _ _ h _ _ => absurd trivial h
  excludes_breach := by
    rintro s rfl
    simp [escapeEngine]

theorem escapeEngine_escape : Escape escapeEngine :=
  ⟨true, Reachable.step (a := ()) (Reachable.init rfl) ⟨rfl, rfl⟩, rfl⟩

/-- Sharpness of `no_clean_proved_with_escape`: without the cleanliness requirement, a
certificate does not exclude escapes. -/
theorem exists_engine_certificate_escape :
    ∃ (S : Type) (A : Type) (e : Engine S A) (_ : Certificate e), Escape e :=
  ⟨Bool, Unit, escapeEngine, escapeCertificate, escapeEngine_escape⟩

/-- Consequently `escapeEngine` has no clean certificate at all. -/
theorem escapeEngine_not_proved : ¬ Proved escapeEngine := fun h =>
  not_escape_of_proved h escapeEngine_escape

/-!
### Finite witnesses

An escape is always exhibited by a concrete finite execution trace, which is what an
isolation engine reports as a counterexample.
-/

/-- `Path e s as s'` : the action list `as` drives the engine from `s` to `s'`. -/
inductive Path (e : Engine S A) : S → List A → S → Prop
  | nil {s : S} : Path e s [] s
  | cons {s : S} {a : A} {s' : S} {as : List A} {s'' : S} :
      e.step s a s' → Path e s' as s'' → Path e s (a :: as) s''

theorem Path.snoc {e : Engine S A} {s s' s'' : S} {as : List A} {a : A}
    (hp : Path e s as s') (hstep : e.step s' a s'') : Path e s (as ++ [a]) s'' := by
  induction hp with
  | nil => exact Path.cons hstep Path.nil
  | cons h _ ih => exact Path.cons h (ih hstep)

theorem Path.reachable {e : Engine S A} {s s' : S} {as : List A}
    (hp : Path e s as s') (hs : Reachable e s) : Reachable e s' := by
  induction hp with
  | nil => exact hs
  | cons hstep _ ih => exact ih (Reachable.step hs hstep)

theorem reachable_iff_exists_path (e : Engine S A) (s : S) :
    Reachable e s ↔ ∃ (s₀ : S) (as : List A), e.init s₀ ∧ Path e s₀ as s := by
  constructor
  · intro h
    induction h with
    | @init s hs => exact ⟨s, [], hs, Path.nil⟩
    | @step s a s' _ hstep ih =>
        obtain ⟨s₀, as, hinit, hp⟩ := ih
        exact ⟨s₀, as ++ [a], hinit, hp.snoc hstep⟩
  · rintro ⟨s₀, as, hinit, hp⟩
    exact hp.reachable (Reachable.init hinit)

/-- **Refutation completeness.** There is an escape iff there is a finite trace from an
initial state to a breach state. -/
theorem escape_iff_exists_witness (e : Engine S A) :
    Escape e ↔ ∃ (s₀ : S) (as : List A) (s : S), e.init s₀ ∧ Path e s₀ as s ∧ e.breach s := by
  constructor
  · rintro ⟨s, hreach, hb⟩
    obtain ⟨s₀, as, hinit, hp⟩ := (reachable_iff_exists_path e s).1 hreach
    exact ⟨s₀, as, s, hinit, hp, hb⟩
  · rintro ⟨s₀, as, s, hinit, hp, hb⟩
    exact ⟨s, (reachable_iff_exists_path e s).2 ⟨s₀, as, hinit, hp⟩, hb⟩

end Isolation
end PCA

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

