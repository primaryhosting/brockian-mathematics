import Mathlib
/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Metric Set
open scoped Real Topology

namespace Frontier

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger) chain
with intracell hopping `v` and intercell hopping `w`:
`h v w k = v + w * exp (I * k)`. -/

theorem ssh_winding_invariant (v w : ℝ) (hw : 0 ≤ w) :
    (|v| ≠ w → ∃ n : ℤ, sshWinding v w = (n : ℂ)) ∧
    (|v| < w → sshWinding v w = 1) ∧
    (w < |v| → sshWinding v w = 0) ∧
    (∀ v' w' : ℝ, 0 ≤ w' →
      ((|v| < w ∧ |v'| < w') ∨ (w < |v| ∧ w' < |v'|)) →
        sshWinding v w = sshWinding v' w') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨1, by simpa using sshWinding_topological h⟩
    · exact ⟨0, by simpa using sshWinding_trivial hw h⟩
  · exact fun h => sshWinding_topological h
  · exact fun h => sshWinding_trivial hw h
  · rintro v' w' hw' (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [sshWinding_topological h1, sshWinding_topological h2]
    · rw [sshWinding_trivial hw h1, sshWinding_trivial hw' h2]

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

