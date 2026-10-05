/-
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- A *global workspace* on a finite state lattice `α`: a broadcast operator
`broadcast : α → α` which is monotone (broadcasting from a larger workspace
content yields a larger workspace content). -/
structure GlobalWorkspace (α : Type*) [Lattice α] [OrderBot α] [Finite α] where
  /-- The broadcast (global-workspace) operator. -/
  broadcast : α → α
  /-- Broadcasting is monotone. -/
  mono : Monotone broadcast

/-- `m` is a least fixed point of `f`: it is a fixed point, and it is below
every fixed point of `f`. -/

theorem exists_iterate_bot_fixed (hf : Monotone f) :
    ∃ n : ℕ, f (f^[n] ⊥) = f^[n] ⊥ := by
  obtain ⟨i, j, hij, hEq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] ⊥)
  -- Without loss of generality `i < j`.
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨i, le_antisymm ?_ ?_⟩
    · have h1 : f^[i + 1] ⊥ ≤ f^[j] ⊥ := iterate_bot_mono hf h
      have h2 : f^[i + 1] ⊥ ≤ f^[i] ⊥ := by rw [hEq]; exact h1
      simpa [Function.iterate_succ_apply'] using h2
    · simpa [Function.iterate_succ_apply'] using iterate_bot_le_succ hf i
  · refine ⟨j, le_antisymm ?_ ?_⟩
    · have h1 : f^[j + 1] ⊥ ≤ f^[i] ⊥ := iterate_bot_mono hf h
      have h2 : f^[j + 1] ⊥ ≤ f^[j] ⊥ := by rw [← hEq]; exact h1
      simpa [Function.iterate_succ_apply'] using h2
    · simpa [Function.iterate_succ_apply'] using iterate_bot_le_succ hf j

omit [Finite α] in
/-- Every iterate of `⊥` lies below every fixed point of a monotone operator. -/
