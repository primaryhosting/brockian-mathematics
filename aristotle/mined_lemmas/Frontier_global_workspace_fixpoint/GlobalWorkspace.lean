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
