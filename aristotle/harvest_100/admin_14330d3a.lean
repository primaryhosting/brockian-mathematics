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
def GlobalWorkspace.stage (W : GlobalWorkspace α) (n : ℕ) : α :=
  W.broadcast^[n] ⊥

@[simp] theorem GlobalWorkspace.stage_zero (W : GlobalWorkspace α) : W.stage 0 = ⊥ := rfl

theorem GlobalWorkspace.stage_succ (W : GlobalWorkspace α) (n : ℕ) :
    W.stage (n + 1) = W.broadcast (W.stage n) :=
  Function.iterate_succ_apply' _ _ _

/-- The broadcast cascade is a monotone (increasing) chain of workspace states. -/
theorem GlobalWorkspace.stage_mono (W : GlobalWorkspace α) : Monotone W.stage := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simp [GlobalWorkspace.stage]
  | succ k ih =>
      rw [W.stage_succ (k + 1)]
      conv_lhs => rw [W.stage_succ k]
      exact W.mono ih

/-- Every stage of the cascade lies below every pre-fixed point of the broadcast operator. -/
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
theorem global_workspace_fixpoint [Finite α] (W : GlobalWorkspace α) :
    ∃ n : ℕ, ∃ p : α, p = W.stage n ∧ W.broadcast p = p ∧
      (∀ q : α, W.broadcast q ≤ q → p ≤ q) ∧
      (∀ q : α, W.broadcast q = q → p ≤ q) := by
  obtain ⟨i, j, hij, hval⟩ := Finite.exists_ne_map_eq_of_infinite W.stage
  -- WLOG `m < n`
  obtain ⟨m, n, hmn, hmn'⟩ : ∃ m n : ℕ, m < n ∧ W.stage m = W.stage n := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hval⟩
    · exact ⟨j, i, h, hval.symm⟩
  have hfix : W.broadcast (W.stage m) = W.stage m := by
    have h1 : W.stage m ≤ W.stage (m + 1) := W.stage_mono (Nat.le_succ m)
    have h2 : W.stage (m + 1) ≤ W.stage n := W.stage_mono hmn
    have := le_antisymm (hmn' ▸ h2) h1
    rw [← W.stage_succ m]
    exact this
  refine ⟨m, W.stage m, rfl, hfix, fun q hq => W.stage_le_of_prefixed hq m,
    fun q hq => W.stage_le_of_prefixed hq.le m⟩

/-- The least fixed point supplied by `OrderHom.lfp` agrees with the stabilised stage of the
broadcast cascade. -/
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

