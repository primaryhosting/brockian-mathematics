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

