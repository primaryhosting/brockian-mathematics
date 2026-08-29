import Mathlib
import RequestProject.GlobalWorkspaceFixpoint

/-!
# Global Workspace Fixpoint — Mathlib interface

A restatement of `Frontier.global_workspace_fixpoint` for Mathlib's order-theoretic
hierarchy: on any finite lattice with a bottom element, a monotone (broadcast)
operator has a least fixed point, reached by finitely many iterations from `⊥`.
-/

namespace Frontier

variable {α : Type*} [Fintype α] [Lattice α] [OrderBot α]

/-- The global workspace attached to a monotone operator on a finite Mathlib lattice. -/

noncomputable def ofMonotone (f : α → α) (hf : Monotone f) : GlobalWorkspace α where
  le a b := a ≤ b
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  sup := (· ⊔ ·)
  le_sup_left := fun _ _ => le_sup_left
  le_sup_right := fun _ _ => le_sup_right
  sup_le := fun h h' => sup_le h h'
  inf := (· ⊓ ·)
  inf_le_left := fun _ _ => inf_le_left
  inf_le_right := fun _ _ => inf_le_right
  le_inf := le_inf
  bot := ⊥
  bot_le := fun _ => bot_le
  elems := Finset.univ.toList
  mem_elems := fun a => Finset.mem_toList.mpr (Finset.mem_univ a)
  bcast := f
  bcast_mono := fun h => hf h

