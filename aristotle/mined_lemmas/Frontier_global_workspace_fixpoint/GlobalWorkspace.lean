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

theorem GlobalWorkspace.stage_le_of_prefixed (W : GlobalWorkspace α) {q : α}
    (hq : W.broadcast q ≤ q) (n : ℕ) : W.stage n ≤ q := by
  induction n with
  | zero => simp
  | succ k ih => exact (W.stage_succ k ▸ (W.mono ih).trans hq)

/-- **Knaster–Tarski for a finite global workspace.**

For a monotone broadcast operator on a finite complete lattice of workspace states,
the broadcast cascade started from the empty workspace `⊥` stabilises after finitely
many steps at a state `p` that is a fixed point of broadcasting and is the least
pre-fixed point (hence the least fixed point) of the operator. -/
