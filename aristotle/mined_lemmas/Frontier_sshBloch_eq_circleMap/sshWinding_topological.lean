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

lemma sshWinding_topological (v w : ℝ) (h : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ ball ((v : ℂ)) w := by
    simp only [mem_ball, Complex.dist_eq, zero_sub, norm_neg, Complex.norm_real,
      Real.norm_eq_abs]
    exact h
  have := circleIntegral.integral_sub_inv_of_mem_ball hmem
  simp only [sub_zero] at this
  rw [sshWinding_eq, this, inv_mul_cancel₀ two_pi_I_ne_zero]

/-- **Trivial phase.**  If `w < |v|` the origin lies outside the loop and the winding
number is `0`. -/
