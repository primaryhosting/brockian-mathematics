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
def IsLeastFixedPoint {α : Type*} [Preorder α] (f : α → α) (m : α) : Prop :=
  f m = m ∧ ∀ x : α, f x = x → m ≤ x

section Iteration

variable {α : Type*} [Lattice α] [OrderBot α] [Finite α] {f : α → α}

omit [Finite α] in
/-- The iterates of a monotone operator started at `⊥` form an increasing chain. -/
theorem iterate_bot_le_succ (hf : Monotone f) (n : ℕ) : f^[n] ⊥ ≤ f^[n + 1] ⊥ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have := hf ih
      simpa [Function.iterate_succ_apply'] using this

omit [Finite α] in
/-- Monotonicity of the iteration chain in the index. -/
theorem iterate_bot_mono (hf : Monotone f) : Monotone (fun n : ℕ => f^[n] ⊥) :=
  monotone_nat_of_le_succ (iterate_bot_le_succ hf)

/-- On a finite lattice, the iteration chain stabilizes: some iterate is a fixed point. -/
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
theorem iterate_bot_le_of_fixed (hf : Monotone f) {x : α} (hx : f x = x) (n : ℕ) :
    f^[n] ⊥ ≤ x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have : f (f^[n] ⊥) ≤ f x := hf ih
      rw [hx] at this
      simpa [Function.iterate_succ_apply'] using this

end Iteration

/--
**Knaster–Tarski for a global workspace.**

A monotone broadcast (global-workspace) operator on a finite state lattice has a
least fixed point, and this least fixed point is *reached* by finitely many
broadcast steps starting from the empty workspace `⊥`.
-/
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

