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

theorem sshWinding_topological {v w : ℝ} (hgap : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ ball (v : ℂ) w := by
    simp [Complex.dist_eq, mem_ball, hgap]
  have hint : (∮ z in C((v : ℂ), w), z⁻¹) = 2 * ↑π * Complex.I := by
    have := circleIntegral.integral_sub_inv_of_mem_ball hmem
    simpa using this
  have hne : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero]
  rw [sshWinding, hint, inv_mul_cancel₀ hne]

/-- **The SSH winding invariant.**

For the SSH chain with hoppings `v` (intracell) and `w ≥ 0` (intercell), the winding number of the
Bloch off-diagonal loop `k ↦ v + w e^{ik}` around the origin is:

* an *integer* whenever the spectrum is gapped (`|v| ≠ w`);
* equal to `1` in the topological phase `|v| < w`;
* equal to `0` in the trivial phase `w < |v|`;
* *invariant* under any change of the parameters that stays inside one and the same phase.

Thus the topological phase of the SSH model is classified by a `ℤ`-valued invariant. -/
