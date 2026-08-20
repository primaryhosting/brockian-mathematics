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

theorem FinEngine.mem_reachFinset_iff (e : FinEngine σ) (s t : σ) :
    t ∈ e.reachFinset s ↔ Reach e.toEngine s t := by
  constructor
  · intro ht
    exact e.mem_iterate_reach s (Fintype.card σ) ht
  · intro ht
    induction ht with
    | refl => exact e.self_mem_reachFinset s
    | tail _ hstep ih =>
        rw [← e.expand_reachFinset s]
        simp only [FinEngine.expand, Finset.mem_union, Finset.mem_biUnion]
        exact Or.inr ⟨_, ih, hstep⟩

/-- **Soundness and completeness of the escape checker.** -/
