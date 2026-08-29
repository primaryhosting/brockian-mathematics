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

theorem monotone_exists_isLeast_fixedPoints (f : α → α) (hf : Monotone f) :
    ∃ n : ℕ, IsLeast {a : α | f a = a} (f^[n] ⊥) := by
  obtain ⟨n, hfix, hleast⟩ := global_workspace_fixpoint (ofMonotone f hf)
  refine ⟨n, ?_, ?_⟩
  · show f (f^[n] ⊥) = f^[n] ⊥
    rw [← ofMonotone_iter f hf n]
    exact hfix
  · intro b hb
    rw [← ofMonotone_iter f hf n]
    exact hleast b hb

end Frontier

/-!
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-- A **finite state lattice**: a finite partially ordered set `α` which is a lattice
(binary joins `sup` and meets `inf`) with a least element `bot`.  Finiteness is
recorded by a list `elems` containing every element. -/
structure StateLattice (α : Type u) where
  /-- The information ordering on workspace states. -/
  le : α → α → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  /-- Binary join (least upper bound). -/
  sup : α → α → α
  le_sup_left : ∀ a b, le a (sup a b)
  le_sup_right : ∀ a b, le b (sup a b)
  sup_le : ∀ {a b c}, le a c → le b c → le (sup a b) c
  /-- Binary meet (greatest lower bound). -/
  inf : α → α → α
  inf_le_left : ∀ a b, le (inf a b) a
  inf_le_right : ∀ a b, le (inf a b) b
  le_inf : ∀ {a b c}, le c a → le c b → le c (inf a b)
  /-- The least element: the empty workspace. -/
  bot : α
  bot_le : ∀ a, le bot a
  /-- A list of all the (finitely many) states. -/
  elems : List α
  mem_elems : ∀ a, a ∈ elems

/-- A **global workspace**: a finite state lattice together with a monotone
*broadcast operator* `bcast`, which sends the current workspace content to the
content resulting from one round of global broadcasting.  Monotonicity says that
broadcasting from a more informative state gives a more informative result. -/
structure GlobalWorkspace (α : Type u) extends StateLattice α where
  /-- The broadcast (global-workspace) operator. -/
  bcast : α → α
  bcast_mono : ∀ {a b}, le a b → le (bcast a) (bcast b)

variable {α : Type u}

/-- `m` is a *least fixed point* of the broadcast operator: it is a fixed point,
and it is below every fixed point. -/
