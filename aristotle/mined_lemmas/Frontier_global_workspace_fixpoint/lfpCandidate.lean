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

noncomputable def lfpCandidate (W : GlobalWorkspace α) : α :=
  (Finset.univ.filter fun b => W.bc b ≤ b).inf id

