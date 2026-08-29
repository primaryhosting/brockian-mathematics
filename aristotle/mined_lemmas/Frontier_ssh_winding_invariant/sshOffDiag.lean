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

noncomputable def sshOffDiag (v w : ℝ) (k : ℝ) : ℂ := (v : ℂ) + (w : ℂ) * Complex.exp (Complex.I * k)

/-- The winding number of the SSH model, defined as the winding number of the loop
`k ↦ sshOffDiag v w k` around the origin, i.e. the contour integral
`(2πi)⁻¹ ∮_{|z - v| = w} dz / z`. -/
