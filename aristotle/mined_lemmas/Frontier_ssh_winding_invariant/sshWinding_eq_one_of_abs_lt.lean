/-
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open Complex Metric

/-- The off-diagonal (inter-sublattice) component of the Bloch Hamiltonian of the
Su–Schrieffer–Heeger (SSH) chain with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w * exp (i k)`.  The full Bloch Hamiltonian is the chiral (off-diagonal) matrix
`[[0, h k], [conj (h k), 0]]`, so its spectral gap is open exactly when `h k ≠ 0` for all `k`. -/

theorem sshWinding_eq_one_of_abs_lt (v w : ℝ) (h : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ ball (v : ℂ) w := by
    have : dist (0 : ℂ) (v : ℂ) = |v| := by
      simp [Complex.dist_eq]
    simpa [Metric.mem_ball, this] using h
  have hI : (∮ z in C((v : ℂ), w), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    have := circleIntegral.integral_sub_inv_of_mem_ball hmem
    simpa using this
  rw [sshWinding_eq_circleIntegral, hI, one_div, inv_mul_cancel₀ two_pi_I_ne_zero]

/-- **Trivial phase.**  If the intracell hopping dominates (`w < |v|`, with `0 ≤ w`) the loop
does not enclose the origin and the winding number is `0`.  The key input is Mathlib's
Cauchy–Goursat theorem `DiffContOnCl.circleIntegral_eq_zero`. -/
