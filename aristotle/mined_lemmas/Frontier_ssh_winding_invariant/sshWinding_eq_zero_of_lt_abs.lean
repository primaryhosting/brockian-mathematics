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

theorem sshWinding_eq_zero_of_lt_abs (v w : ℝ) (hw : 0 ≤ w) (h : w < |v|) :
    sshWinding v w = 0 := by
  have hne : ∀ z ∈ closedBall (v : ℂ) w, z ≠ 0 := by
    intro z hz hz0
    have : dist (0 : ℂ) (v : ℂ) ≤ w := by
      simpa [hz0] using hz
    have hv : |v| ≤ w := by
      simpa [Complex.dist_eq] using this
    exact absurd hv (not_le.2 h)
  have hdc : DiffContOnCl ℂ (fun z : ℂ => z⁻¹) (ball (v : ℂ) w) := by
    constructor
    · intro z hz
      exact (differentiableAt_inv (hne z (ball_subset_closedBall hz))).differentiableWithinAt
    · intro z hz
      have hz' : z ∈ closedBall (v : ℂ) w := closure_ball_subset_closedBall hz
      exact (continuousAt_inv₀ (hne z hz')).continuousWithinAt
  have hI : (∮ z in C((v : ℂ), w), z⁻¹) = 0 := hdc.circleIntegral_eq_zero hw
  rw [sshWinding_eq_circleIntegral, hI, mul_zero]

/-- **The SSH topological invariant.**

For a gapped SSH chain (intercell hopping `w ≥ 0`, intracell hopping `v`, gap condition
`|v| ≠ w`) the winding number `W = (2πi)⁻¹ ∫₀^{2π} h'(k)/h(k) dk` of the Bloch loop
`h k = v + w e^{ik}` is an *integer*: it equals `1` in the topological phase `|v| < w`
and `0` in the trivial phase `w < |v|`. -/
