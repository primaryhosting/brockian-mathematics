import Mathlib

/-!
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Classical

/-- A **global workspace** on a finite state lattice `α`: a broadcast operator
`bc : α → α` which is monotone (more information broadcast in, more information out). -/
structure GlobalWorkspace (α : Type*) [Fintype α] [Lattice α] [BoundedOrder α] where
  /-- The broadcast operator of the workspace. -/
  bc : α → α
  /-- Broadcasting is monotone. -/
  mono : Monotone bc

variable {α : Type*} [Fintype α] [Lattice α] [BoundedOrder α]

/-- `a` is a fixed point of the broadcast operator: a stable global workspace content. -/

lemma le_bc_lfpCandidate (W : GlobalWorkspace α) :
    lfpCandidate W ≤ W.bc (lfpCandidate W) :=
  lfpCandidate_le_of_prefixed (W.mono (bc_lfpCandidate_le W))

/-- **Knaster–Tarski for a global workspace.**
A monotone broadcast operator on a finite state lattice has a least fixed point. -/
