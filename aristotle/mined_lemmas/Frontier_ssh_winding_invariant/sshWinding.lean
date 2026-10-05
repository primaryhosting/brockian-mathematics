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

noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * ↑π * Complex.I)⁻¹ * ∮ z in C((v : ℂ), w), z⁻¹

/-- The contour-integral definition of the winding number agrees with the usual physics formula
`(2πi)⁻¹ ∫₀^{2π} h'(k) / h(k) dk` for the SSH loop `h k = v + w e^{ik}`. -/
