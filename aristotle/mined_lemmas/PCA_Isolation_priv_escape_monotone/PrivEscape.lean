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

def PrivEscape (e : Engine σ) (s : σ) : Prop :=
  ∃ t, Reach e s t ∧ t ∉ e.trusted

/-- `Refines e₁ e₂` says that `e₂` is at least as permissive as `e₁`: it allows all the
transitions `e₁` allows and its isolation boundary is no larger. -/
structure Refines (e₁ e₂ : Engine σ) : Prop where
  /-- Every transition of `e₁` is a transition of `e₂`. -/
  step_le : ∀ a b, e₁.step a b → e₂.step a b
  /-- The isolation boundary of `e₂` is contained in that of `e₁`. -/
  trusted_subset : e₂.trusted ⊆ e₁.trusted

