/-
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-!`, so the mandated
-- header above is kept verbatim as a plain block comment and repeated as a module docstring.)

import Mathlib

/-!
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A **global workspace** on a finite state lattice `α`: a monotone *broadcast* operator
`broadcast : α → α`.  A state `x : α` records which contents are currently globally
available; `broadcast x` is the state obtained after one round of competition and
broadcast.  Monotonicity says that making more content available can only make more
content available after broadcasting. -/
structure GlobalWorkspace (α : Type*) [CompleteLattice α] [Fintype α] where
  /-- One round of global broadcast. -/
  broadcast : α → α
  /-- Broadcasting is monotone. -/
  mono : Monotone broadcast

variable {α : Type*} [CompleteLattice α] [Fintype α]

/-- The broadcast operator packaged as an order homomorphism. -/
def GlobalWorkspace.toOrderHom (W : GlobalWorkspace α) : α →o α :=
  ⟨W.broadcast, W.mono⟩

/-- The *ignition* sequence: iterating broadcast from the empty workspace `⊥`. -/
def GlobalWorkspace.ignition (W : GlobalWorkspace α) (n : ℕ) : α :=
  W.broadcast^[n] ⊥

/-- A state is a *stable workspace* (fixed point) if broadcasting does not change it. -/
def GlobalWorkspace.IsStable (W : GlobalWorkspace α) (x : α) : Prop :=
  W.broadcast x = x

/-- The least fixed point of the broadcast operator. -/
def GlobalWorkspace.leastStable (W : GlobalWorkspace α) : α :=
  OrderHom.lfp W.toOrderHom

theorem GlobalWorkspace.ignition_zero (W : GlobalWorkspace α) : W.ignition 0 = ⊥ := rfl

theorem GlobalWorkspace.ignition_succ (W : GlobalWorkspace α) (n : ℕ) :
    W.ignition (n + 1) = W.broadcast (W.ignition n) := by
  simp [ignition, Function.iterate_succ_apply']

/-- The ignition sequence is monotone. -/
theorem GlobalWorkspace.ignition_monotone (W : GlobalWorkspace α) : Monotone W.ignition := by
  have step : ∀ n, W.ignition n ≤ W.ignition (n + 1) := by
    intro n
    induction n with
    | zero => simp [ignition]
    | succ k ih =>
        rw [ignition_succ, ignition_succ (n := k + 1)]
        exact W.mono ih
  exact monotone_nat_of_le_succ step

/-- Every ignition stage is below any stable state, in particular below the least fixed point. -/
theorem GlobalWorkspace.ignition_le_of_broadcast_le (W : GlobalWorkspace α) {x : α}
    (hx : W.broadcast x ≤ x) (n : ℕ) : W.ignition n ≤ x := by
  induction n with
  | zero => simp [ignition]
  | succ k ih => exact (ignition_succ W k) ▸ le_trans (W.mono ih) hx

/-- On a finite lattice the ignition sequence stabilizes after finitely many rounds. -/
theorem GlobalWorkspace.exists_ignition_stable (W : GlobalWorkspace α) :
    ∃ n : ℕ, W.ignition (n + 1) = W.ignition n := by
  by_contra h
  push_neg at h
  have hstrict : StrictMono W.ignition := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    exact lt_of_le_of_ne (W.ignition_monotone (Nat.le_succ n)) (Ne.symm (h n))
  exact not_injective_infinite_finite W.ignition hstrict.injective

/-!
## Main theorem
-/

/-- **Global workspace fixpoint (Knaster–Tarski, finite state lattice).**

A monotone broadcast operator `W.broadcast` on a finite state lattice `α` has a least fixed
point `W.leastStable`, and this least fixed point is *reached* by finitely many rounds of
broadcasting starting from the empty workspace `⊥`.

Concretely, there is a stage `n` such that:
* `W.leastStable` is stable (a fixed point of broadcast);
* `W.leastStable` is below every stable state (indeed below every pre-fixed point);
* the ignition sequence has converged at stage `n`, and its value there is exactly
  `W.leastStable`, and it stays there forever after. -/
theorem global_workspace_fixpoint (W : GlobalWorkspace α) :
    W.IsStable W.leastStable ∧
    (∀ x : α, W.IsStable x → W.leastStable ≤ x) ∧
    ∃ n : ℕ, W.ignition n = W.leastStable ∧ ∀ m : ℕ, n ≤ m → W.ignition m = W.leastStable := by
  have hfix : W.broadcast W.leastStable = W.leastStable :=
    OrderHom.map_lfp W.toOrderHom
  have hleast : ∀ x : α, W.broadcast x ≤ x → W.leastStable ≤ x := fun x hx =>
    OrderHom.lfp_le W.toOrderHom hx
  obtain ⟨n, hn⟩ := W.exists_ignition_stable
  -- the stabilized stage is a fixed point, hence above `leastStable`
  have hstable : W.broadcast (W.ignition n) = W.ignition n := by
    rw [← W.ignition_succ n]; exact hn
  have h1 : W.leastStable ≤ W.ignition n := hleast _ (le_of_eq hstable)
  have h2 : W.ignition n ≤ W.leastStable :=
    W.ignition_le_of_broadcast_le (le_of_eq hfix) n
  have hval : W.ignition n = W.leastStable := le_antisymm h2 h1
  refine ⟨hfix, fun x hx => hleast x (le_of_eq hx), n, hval, ?_⟩
  intro m hm
  refine le_antisymm ?_ ?_
  · exact W.ignition_le_of_broadcast_le (le_of_eq hfix) m
  · exact hval ▸ W.ignition_monotone hm

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

