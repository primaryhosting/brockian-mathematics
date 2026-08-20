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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Complex Metric

/-- The (analytically continued) off-diagonal entry of the SSH Bloch Hamiltonian.
With `z = exp (I * k)` on the unit circle, `sshBloch v w z = v + w * z` is the
intra-cell/inter-cell hopping combination `v + w * e^{i k}`. -/

theorem ssh_gapped (v w : ℂ) (hgap : ‖v‖ ≠ ‖w‖) (k : ℝ) :
    sshBloch v w (Complex.exp (k * Complex.I)) ≠ 0 := by
  intro h0
  have hz : ‖Complex.exp (k * Complex.I)‖ = 1 := by simp [Complex.norm_exp_ofReal_mul_I]
  have hv : v = -(w * Complex.exp (k * Complex.I)) := by
    have : v + w * Complex.exp (k * Complex.I) = 0 := h0
    linear_combination this
  apply hgap
  rw [hv, norm_neg, norm_mul, hz, mul_one]

/-- Away from the gap-closing point `‖v‖ = ‖w‖`, the SSH winding number is an integer:
it takes the value `1` (topological phase) or `0` (trivial phase). -/
