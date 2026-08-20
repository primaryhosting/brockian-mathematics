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
# A formal model of a predicate-based isolation engine

This file develops a small but complete formal model of the *isolation engine* underlying a
predicate/component analysis (`PCA`): an engine observes a state space `σ`, carries a finite list
of *isolation guards* (side conditions that the engine may additionally assume/enforce), and
*tightens* a user-supplied predicate by conjoining those guards.

The central correctness statement is
`PCA.Isolation.tightened_predicate_refines_original`: tightening is always a *refinement*, i.e.
every state admitted by the tightened predicate is admitted by the original one.  This is the
soundness half of the model.  The completeness half
(`PCA.Isolation.original_refines_tightened_of_guards_valid`) says that when the guards are already
implied by the original predicate, the tightened predicate admits exactly as much as the original,
so tightening loses no information.

Beyond the two halves we record the algebraic structure of tightening (monotonicity,
idempotence, greatest-lower-bound characterisation), its interaction with the transition relation
(inductive invariants and reachability), and the fact that the engine never isolates a state
"for no reason".
-/

namespace PCA
namespace Isolation

variable {σ : Type*}

/-- A predicate over the engine's state space: the engine's model of a set of states. -/

theorem tighten_append_refines (step : σ → σ → Prop) (gs hs' : List (Pred σ)) (P : Pred σ) :
    Refines (Engine.tighten ⟨step, gs ++ hs'⟩ P) (Engine.tighten ⟨step, gs⟩ P) := by
  intro s h
  refine ⟨h.1, fun g hg => h.2 g ?_⟩
  exact List.mem_append_left _ hg

/-! ## Interaction with the transition relation -/

/-- If both the original predicate and the guard conjunction are inductive invariants, so is the
tightened predicate. -/
