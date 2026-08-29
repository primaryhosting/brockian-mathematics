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

theorem global_workspace_fixpoint {α : Type*} [Lattice α] [OrderBot α] [Finite α]
    (W : GlobalWorkspace α) :
    ∃ m : α, IsLeastFixedPoint W.broadcast m ∧ ∃ n : ℕ, m = W.broadcast^[n] ⊥ := by
  obtain ⟨n, hn⟩ := exists_iterate_bot_fixed W.mono
  refine ⟨W.broadcast^[n] ⊥, ⟨hn, ?_⟩, ⟨n, rfl⟩⟩
  intro x hx
  exact iterate_bot_le_of_fixed W.mono hx n

/-- The hypotheses are satisfiable: powersets of a finite type of "contents"
form a finite state lattice, and e.g. the operator adjoining a fixed broadcast
content is monotone. -/
example (k : ℕ) (c : Fin k) :
    ∃ m : Set (Fin k),
      IsLeastFixedPoint (fun s : Set (Fin k) => insert c s) m ∧
        ∃ n : ℕ, m = (fun s : Set (Fin k) => insert c s)^[n] ⊥ :=
  global_workspace_fixpoint
    { broadcast := fun s => insert c s
      mono := fun _ _ h => Set.insert_subset_insert h }

end Frontier

