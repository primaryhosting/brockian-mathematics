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

theorem escapeCheck_iff (e : FinEngine σ) (s : σ) :
    e.escapeCheck s = true ↔ PrivEscape e.toEngine s := by
  have hcheck : (e.escapeCheck s = true) ↔ ¬ (e.reachFinset s ⊆ e.trusted) := by
    simp [FinEngine.escapeCheck]
  rw [hcheck, Finset.not_subset]
  constructor
  · rintro ⟨t, ht, hnt⟩
    exact ⟨t, (e.mem_reachFinset_iff s t).1 ht, by simpa [FinEngine.toEngine] using hnt⟩
  · rintro ⟨t, ht, hnt⟩
    exact ⟨t, (e.mem_reachFinset_iff s t).2 ht, by simpa [FinEngine.toEngine] using hnt⟩

/-- Privilege escape is decidable for finite-state engines. -/
instance (e : FinEngine σ) (s : σ) : Decidable (PrivEscape e.toEngine s) :=
  decidable_of_iff _ (escapeCheck_iff e s)

/-! ### A worked example

A three-state engine: state `0` is the sandboxed task, state `1` an intermediate
privileged helper and state `2` the (untrusted) kernel. Only states `0` and `1` are
trusted, and the engine allows `0 → 1 → 2`, so the sandbox can escape. Hardening the
engine by removing the transition `1 → 2` removes the escape. -/
section Example

/-- The permissive engine `0 → 1 → 2` with `{0, 1}` trusted. -/
