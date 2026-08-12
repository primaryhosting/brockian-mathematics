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
def stage (n : ℕ) : α := W.broadcast^[n] ⊥

@[simp] theorem stage_zero : W.stage 0 = (⊥ : α) := rfl

@[simp] theorem stage_succ (n : ℕ) : W.stage (n + 1) = W.broadcast (W.stage n) := by
  simp [stage, Function.iterate_succ_apply']

/-- The broadcast cascade is increasing at each step. -/
theorem stage_le_succ (n : ℕ) : W.stage n ≤ W.stage (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [stage_succ, stage_succ]
      exact W.mono ih

/-- The broadcast cascade is a monotone chain. -/
theorem stage_mono : Monotone (W.stage) :=
  monotone_nat_of_le_succ (W.stage_le_succ)

/-- Once the cascade repeats a stage, it has reached a fixed point. -/
theorem broadcast_fixed_of_stage_succ_eq {n : ℕ} (h : W.stage (n + 1) = W.stage n) :
    W.broadcast (W.stage n) = W.stage n := by
  rw [← stage_succ]; exact h

/-- Every stage of the cascade is below every prefixed point of the broadcast operator. -/
theorem stage_le_of_prefixed {y : α} (hy : W.broadcast y ≤ y) (n : ℕ) : W.stage n ≤ y := by
  induction n with
  | zero => simp
  | succ n ih => exact (stage_succ W n ▸ (W.mono ih).trans hy)

variable [Fintype α]

/-- On a finite lattice the cascade stabilises after at most `Fintype.card α` steps. -/
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
theorem exists_least_fixpoint_of_broadcast :
    ∃ x : α, W.broadcast x = x ∧ (∀ y : α, W.broadcast y ≤ y → x ≤ y) ∧
      ∃ n ≤ Fintype.card α, W.broadcast^[n] ⊥ = x := by
  obtain ⟨n, hn, hstab⟩ := W.exists_stage_stabilises
  refine ⟨W.stage n, W.broadcast_fixed_of_stage_succ_eq hstab, ?_, ⟨n, hn, rfl⟩⟩
  intro y hy
  exact W.stage_le_of_prefixed hy n

end GlobalWorkspace

/--
**Knaster–Tarski for a global workspace.**

A monotone broadcast (global-workspace) operator `W.broadcast` on a finite state
lattice `α` reaches a least fixed point: there is a state `x` with
`W.broadcast x = x` which lies below every prefixed point `y`
(i.e. `W.broadcast y ≤ y`), and in particular below every fixed point.
Moreover this least fixed point is reached in finitely many broadcast rounds:
`x = W.broadcast^[n] ⊥` for some `n ≤ Fintype.card α`, starting from the empty
workspace `⊥`.
-/
theorem global_workspace_fixpoint [Lattice α] [BoundedOrder α] [Fintype α]
    (W : GlobalWorkspace α) :
    ∃ x : α,
      W.broadcast x = x ∧
      (∀ y : α, W.broadcast y ≤ y → x ≤ y) ∧
      (∀ y : α, W.broadcast y = y → x ≤ y) ∧
      ∃ n ≤ Fintype.card α, W.broadcast^[n] ⊥ = x := by
  obtain ⟨x, hfix, hpre, hreach⟩ := W.exists_least_fixpoint_of_broadcast
  exact ⟨x, hfix, hpre, fun y hy => hpre y hy.le, hreach⟩

end

end Frontier

/-! ### A concrete instance, showing the hypotheses are satisfiable -/

namespace Example

/-- Broadcasting on the lattice of subsets of a three-module system: whatever is
already in the workspace stays, and module `0` always gets broadcast. -/
def broadcastAdjoinZero (s : Finset (Fin 3)) : Finset (Fin 3) := insert 0 s

/-- The concrete global workspace built from `broadcastAdjoinZero`. -/
def W3 : Frontier.GlobalWorkspace (Finset (Fin 3)) where
  broadcast := broadcastAdjoinZero
  mono := fun _ _ h => Finset.insert_subset_insert _ h

example : ∃ x : Finset (Fin 3),
    W3.broadcast x = x ∧
    (∀ y : Finset (Fin 3), W3.broadcast y ≤ y → x ≤ y) ∧
    (∀ y : Finset (Fin 3), W3.broadcast y = y → x ≤ y) ∧
    ∃ n ≤ Fintype.card (Finset (Fin 3)), W3.broadcast^[n] ⊥ = x :=
  Frontier.global_workspace_fixpoint W3

end Example

#print axioms Frontier.global_workspace_fixpoint

