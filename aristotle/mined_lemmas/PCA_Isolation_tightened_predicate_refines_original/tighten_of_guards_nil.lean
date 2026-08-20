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

theorem tighten_of_guards_nil (E : Engine σ) (P : Pred σ) (h : E.guards = []) :
    E.tighten P = P := by
  apply tighten_eq_of_guards_valid
  intro s _ g hg
  rw [h] at hg
  exact absurd hg (List.not_mem_nil)

/-! ## Algebraic structure of tightening -/

/-- Tightening is monotone in the predicate it is applied to. -/
