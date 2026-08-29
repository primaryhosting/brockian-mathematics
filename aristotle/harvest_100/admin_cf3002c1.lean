/-
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean requires `import` to be the
-- first command in a file; the same text is repeated as a module docstring below.)

import Mathlib

/-!
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A *global workspace* (broadcast) system on a state lattice `α`: a monotone operator
`op` that takes the current global state to the state after one round of broadcast. -/
structure Broadcast (α : Type*) [Lattice α] where
  /-- The broadcast operator. -/
  op : α → α
  /-- Broadcasting is monotone: more information in, more information out. -/
  mono : Monotone op

variable {α : Type*} [Lattice α] [OrderBot α]

/-- The `n`-th broadcast round starting from the empty workspace `⊥`. -/
def Broadcast.iter (W : Broadcast α) (n : ℕ) : α := W.op^[n] ⊥

@[simp] lemma Broadcast.iter_zero (W : Broadcast α) : W.iter 0 = ⊥ := rfl

lemma Broadcast.iter_succ (W : Broadcast α) (n : ℕ) : W.iter (n + 1) = W.op (W.iter n) := by
  simp [Broadcast.iter, Function.iterate_succ_apply']

/-- The broadcast orbit starting from `⊥` is monotone in the number of rounds. -/
lemma Broadcast.monotone_iter (W : Broadcast α) : Monotone W.iter := by
  have step : ∀ n : ℕ, W.iter n ≤ W.iter (n + 1) := by
    intro n
    induction n with
    | zero => simp [Broadcast.iter_succ]
    | succ k ih =>
        rw [W.iter_succ k, W.iter_succ (k + 1)]
        exact W.mono ih
  exact monotone_nat_of_le_succ step

/-- Any pre-fixed point of the broadcast operator dominates every stage of the orbit. -/
lemma Broadcast.iter_le_of_op_le (W : Broadcast α) {b : α} (hb : W.op b ≤ b) (n : ℕ) :
    W.iter n ≤ b := by
  induction n with
  | zero => simp
  | succ k ih => exact (W.iter_succ k ▸ (W.mono ih).trans hb)

/-- **Knaster–Tarski for a finite global workspace.**
A monotone broadcast operator on a finite state lattice reaches a least fixed point:
there is a state `a` that is invariant under broadcasting, is below every pre-fixed point
(in particular below every fixed point), and is attained after finitely many broadcast
rounds started from the empty workspace `⊥`. -/
theorem global_workspace_fixpoint {α : Type*} [Lattice α] [OrderBot α] [Finite α]
    (W : Broadcast α) :
    ∃ a : α, W.op a = a ∧ (∀ b : α, W.op b ≤ b → a ≤ b) ∧ ∃ n : ℕ, a = W.iter n := by
  obtain ⟨i, j, hij, hfe⟩ := Finite.exists_ne_map_eq_of_infinite W.iter
  -- WLOG `i < j`; monotonicity then forces the orbit to be stationary at `i`.
  have key : ∀ p q : ℕ, p < q → W.iter p = W.iter q → W.op (W.iter p) = W.iter p := by
    intro p q hpq he
    have h1 : W.iter p ≤ W.iter (p + 1) := W.monotone_iter (Nat.le_succ p)
    have h2 : W.iter (p + 1) ≤ W.iter q := W.monotone_iter hpq
    have : W.iter (p + 1) = W.iter p := le_antisymm (he ▸ h2) h1
    rw [← W.iter_succ p, this]
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨W.iter i, key i j h hfe, fun b hb => W.iter_le_of_op_le hb i, i, rfl⟩
  · exact ⟨W.iter j, key j i h hfe.symm, fun b hb => W.iter_le_of_op_le hb j, j, rfl⟩

end Frontier

