import Mathlib

/-!
# Global workspace: existence of a least fixed point (Knaster–Tarski, finite case)

We model a *global workspace* as a finite complete lattice `α` of workspace states
together with a monotone *broadcast* operator `broadcast : α → α`.

The main theorem `Frontier.global_workspace_fixpoint` states that iterating the
broadcast operator from the empty workspace `⊥` reaches, after finitely many steps,
a state `p` which is
* a fixed point of the broadcast operator (`broadcast p = p`), and
* the *least* pre-fixed point: `p ≤ q` for every `q` with `broadcast q ≤ q`
  (in particular `p ≤ q` for every fixed point `q`).

This is the finite (constructive-by-iteration) form of the Knaster–Tarski theorem.
-/

namespace Frontier

/-- A **global workspace** on a state lattice `α`: a broadcast operator that is
monotone, i.e. broadcasting from a larger workspace state yields a larger state. -/
structure GlobalWorkspace (α : Type*) [CompleteLattice α] where
  /-- The broadcast (global-workspace) operator. -/
  broadcast : α → α
  /-- Broadcasting is monotone. -/
  mono : Monotone broadcast

variable {α : Type*} [CompleteLattice α]

/-- The `n`-th stage of the broadcast cascade, starting from the empty workspace `⊥`. -/

theorem global_workspace_lfp_eq_stage [Finite α] (W : GlobalWorkspace α) :
    ∃ n : ℕ, OrderHom.lfp ⟨W.broadcast, W.mono⟩ = W.stage n := by
  obtain ⟨n, p, hp, hfix, hle, -⟩ := global_workspace_fixpoint W
  refine ⟨n, ?_⟩
  refine le_antisymm ?_ ?_
  · exact hp ▸ OrderHom.lfp_le _ (le_of_eq hfix)
  · exact hp ▸ hle _ (le_of_eq (OrderHom.map_lfp ⟨W.broadcast, W.mono⟩))

end Frontier

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

