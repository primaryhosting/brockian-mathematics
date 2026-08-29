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

lemma ofMonotone_iter (f : α → α) (hf : Monotone f) (n : ℕ) :
    (ofMonotone f hf).iter n = f^[n] ⊥ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [GlobalWorkspace.iter, ih, Function.iterate_succ_apply']
      rfl

/-- **Knaster–Tarski, Mathlib form.** A monotone broadcast operator on a finite lattice
with least element has a least fixed point, and it is `f^[n] ⊥` for some `n`. -/
