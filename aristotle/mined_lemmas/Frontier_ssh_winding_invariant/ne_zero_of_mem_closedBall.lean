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

theorem ne_zero_of_mem_closedBall {v w : ℝ} (hgap : w < |v|) {z : ℂ}
    (hz : z ∈ closedBall (v : ℂ) w) : z ≠ 0 := by
  have hd : ‖z - (v : ℂ)‖ ≤ w := by
    simpa [Complex.dist_eq] using (mem_closedBall.mp hz)
  have hv : ‖(v : ℂ)‖ = |v| := by simp
  have : |v| - ‖z - (v : ℂ)‖ ≤ ‖z‖ := by
    have := norm_sub_norm_le (v : ℂ) (v - z)
    have h2 : ‖(v : ℂ) - ((v : ℂ) - z)‖ = ‖z‖ := by ring_nf
    have h3 : ‖(v : ℂ) - z‖ = ‖z - (v : ℂ)‖ := norm_sub_rev _ _
    rw [h2, h3, hv] at this
    exact this
  have hpos : 0 < ‖z‖ := lt_of_lt_of_le (by linarith) this
  simpa using norm_pos_iff.mp hpos

/-- **Trivial phase.** If the intracell hopping dominates (`w < |v|`) the origin lies outside the
loop and the winding number vanishes. -/
