import Mathlib

/-!
# A formal model of an isolation engine

This file develops a small but complete formal model of the "isolation engine" of a
*privilege-controlled architecture* (`PCA`).

An `Engine` is a (possibly infinite) transition system on a type of machine states
together with a distinguished set of *trusted* states (the isolation boundary).
A *privilege escape* from a state `s` is the existence of a run of the engine starting
at `s` and ending outside the isolation boundary.

The main results are:

* `PCA.Isolation.priv_escape_monotone` — escapes are monotone along refinement: making
  the engine more permissive (more transitions, fewer trusted states) can only create
  escapes, never remove them.
* `PCA.Isolation.isolation_sound` / `PCA.Isolation.isolation_complete` — an inductive
  invariant contained in the isolation boundary is a sound *and* complete certificate of
  the absence of privilege escapes.
* `PCA.Isolation.escapeCheck_iff` — for a finite-state engine the explicit reachability
  computation `escapeCheck` decides privilege escape: it is sound and complete with
  respect to the relational semantics.
-/

namespace PCA.Isolation

universe u

/-- An isolation engine on a state space `σ`: a transition relation `step` describing the
runs the engine permits, together with the set `trusted` of states that lie inside the
isolation boundary. -/
structure Engine (σ : Type u) where
  /-- The transitions the engine permits. -/
  step : σ → σ → Prop
  /-- The isolation boundary: the states considered privilege-safe. -/
  trusted : Set σ

variable {σ : Type u}

/-- `Reach e s t` says that the engine `e` admits a (possibly empty) run from `s` to `t`. -/

theorem hardened_refines_leaky : Refines hardenedEngine.toEngine leakyEngine.toEngine := by
  constructor
  · intro a b h
    fin_cases a <;>
      simp_all [FinEngine.toEngine, hardenedEngine, leakyEngine]
  · intro x hx
    exact hx

end Example

end PCA.Isolation

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

