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

def boolWorkspace : GlobalWorkspace Bool where
  le a b := a = true → b = true
  le_refl := by intro a h; exact h
  le_trans := by intro a b c hab hbc h; exact hbc (hab h)
  le_antisymm := by intro a b hab hba; revert hab hba; cases a <;> cases b <;> simp
  sup a b := a || b
  le_sup_left := by intro a b h; simp [h]
  le_sup_right := by intro a b h; simp [h]
  sup_le := by intro a b c hac hbc h; revert hac hbc h; cases a <;> cases b <;> simp
  inf a b := a && b
  inf_le_left := by intro a b h; revert h; cases a <;> cases b <;> simp
  inf_le_right := by intro a b h; revert h; cases a <;> cases b <;> simp
  le_inf := by intro a b c hca hcb h; simp [hca h, hcb h]
  bot := false
  bot_le := by intro a h; simp at h
  elems := [false, true]
  mem_elems := by decide
  bcast a := a
  bcast_mono := by intro a b h; exact h

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

