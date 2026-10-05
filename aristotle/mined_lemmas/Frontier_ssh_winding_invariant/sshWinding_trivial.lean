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

theorem sshWinding_trivial {v w : ℝ} (hw : 0 ≤ w) (hgap : w < |v|) : sshWinding v w = 0 := by
  have hzero : (∮ z in C((v : ℂ), w), z⁻¹) = 0 := by
    refine DiffContOnCl.circleIntegral_eq_zero hw ?_
    constructor
    · intro z hz
      have hz0 : z ≠ 0 := ne_zero_of_mem_closedBall hgap (ball_subset_closedBall hz)
      exact ((differentiableAt_inv_iff.mpr hz0).differentiableWithinAt)
    · intro z hz
      have hz0 : z ≠ 0 :=
        ne_zero_of_mem_closedBall hgap (closure_ball_subset_closedBall hz)
      exact ((differentiableAt_inv_iff.mpr hz0).continuousAt).continuousWithinAt
  simp [sshWinding, hzero]

/-- **Topological phase.** If the intercell hopping dominates (`|v| < w`) the origin lies inside the
loop and the winding number equals `1`. -/
