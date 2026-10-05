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

theorem sshWinding_eq_phase_integral (v w : ℝ) :
    sshWinding v w =
      (2 * ↑π * Complex.I)⁻¹ *
        ∫ k in (0 : ℝ)..(2 * π), (Complex.I * w * Complex.exp (Complex.I * k)) / sshOffDiag v w k := by
  unfold sshWinding sshOffDiag circleIntegral
  congr 1
  refine intervalIntegral.integral_congr fun k _ => ?_
  simp only [deriv_circleMap, circleMap, smul_eq_mul, div_eq_mul_inv]
  ring_nf

/-- **The gap condition.** The SSH loop `k ↦ v + w e^{ik}` misses the origin (equivalently, the
Bloch Hamiltonian is gapped) exactly when `|v| ≠ w`. -/
