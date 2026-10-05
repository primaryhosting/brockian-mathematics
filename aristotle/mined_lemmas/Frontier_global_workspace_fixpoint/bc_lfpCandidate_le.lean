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

lemma bc_lfpCandidate_le (W : GlobalWorkspace α) :
    W.bc (lfpCandidate W) ≤ lfpCandidate W := by
  refine Finset.le_inf ?_
  intro b hb
  have hb' : W.bc b ≤ b := by simpa using hb
  exact le_trans (W.mono (lfpCandidate_le_of_prefixed hb')) hb'

