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
# Knaster–Tarski for a global workspace (broadcast) operator

A *global workspace* over a finite state lattice `α` consists of a `broadcast`
operator `α → α` which is monotone: enriching the current workspace content can
only enrich what gets broadcast.

The main theorem `Frontier.global_workspace_fixpoint` states that such an
operator has a least fixed point, which is moreover reached by iterating the
operator finitely many times (at most `Fintype.card α` times) starting from the
empty workspace `⊥`.
-/

namespace Frontier

variable {α : Type*}

/-- A **global workspace** on a state lattice `α`: a monotone broadcast operator. -/
structure GlobalWorkspace (α : Type*) [Lattice α] [BoundedOrder α] where
  /-- The broadcast operator: given the current workspace state, the new state. -/
  broadcast : α → α
  /-- Broadcasting is monotone in the workspace content. -/
  mono : Monotone broadcast

section

namespace GlobalWorkspace

variable [Lattice α] [BoundedOrder α] (W : GlobalWorkspace α)

/-- The `n`-th stage of the broadcast cascade, started from the empty workspace `⊥`. -/

theorem exists_stage_stabilises :
    ∃ n ≤ Fintype.card α, W.stage (n + 1) = W.stage n := by
  have hcard : Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by
    simp
  obtain ⟨i, j, hij, hEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (Fintype.card α + 1) => W.stage i) hcard
  -- WLOG `i < j`
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨(i : ℕ), ?_, le_antisymm ?_ (W.stage_le_succ i)⟩
    · omega
    · calc W.stage ((i : ℕ) + 1) ≤ W.stage (j : ℕ) := W.stage_mono (by omega)
        _ = W.stage (i : ℕ) := hEq.symm
  · refine ⟨(j : ℕ), ?_, le_antisymm ?_ (W.stage_le_succ j)⟩
    · omega
    · calc W.stage ((j : ℕ) + 1) ≤ W.stage (i : ℕ) := W.stage_mono (by omega)
        _ = W.stage (j : ℕ) := hEq

/--
**Knaster–Tarski for a global workspace.**

A monotone broadcast operator on a finite state lattice has a least fixed point
`x`; indeed `x` is below every prefixed point (`broadcast y ≤ y`), and hence
below every fixed point. Moreover `x` is reached by iterating the broadcast
operator at most `Fintype.card α` times starting from the empty workspace `⊥`.
-/
