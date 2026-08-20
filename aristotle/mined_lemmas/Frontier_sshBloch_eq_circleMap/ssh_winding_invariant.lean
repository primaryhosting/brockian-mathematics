import Mathlib

/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
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

set_option grind.warning false

namespace Frontier

open Complex Metric

/-- The off-diagonal entry of the Bloch Hamiltonian of the Su-Schrieffer-Heeger (SSH) chain
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  Chiral (sublattice) symmetry forces the Bloch Hamiltonian to be
off-diagonal, so the whole topological content of the model is carried by this loop
`k ↦ h(k)` in the complex plane. -/

theorem ssh_winding_invariant (v w : ℝ) (hw : 0 < w) :
    (|v| < w → sshWinding v w = ((1 : ℤ) : ℂ)) ∧
      (w < |v| → sshWinding v w = ((0 : ℤ) : ℂ)) := by
  constructor
  · intro h
    simpa using sshWinding_topological v w h
  · intro h
    simpa using sshWinding_trivial v w hw.le h

end Frontier

