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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Complex intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger)
chain with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The two-band Hamiltonian is
`H(k) = [[0, h(k)], [conj (h k), 0]]`, whose spectral gap is open iff `h k ≠ 0`. -/

theorem sshWinding_eq_zero (v w : ℝ) (hw : 0 < w) (hvw : w < |v|) :
    sshWinding v w = 0 := by
  have hne : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (v : ℂ) + (w : ℂ) * z ≠ 0 := by
    intro z hz hz0
    have hzle : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have h1 : ‖(w : ℂ) * z‖ ≤ w := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
      calc w * ‖z‖ ≤ w * 1 := by
            exact mul_le_mul_of_nonneg_left hzle hw.le
        _ = w := by ring
    have h2 : ((v : ℂ)) = -((w : ℂ) * z) := by
      linear_combination hz0
    have h3 : |v| ≤ w := by
      have : ‖(v : ℂ)‖ ≤ w := by rw [h2, norm_neg]; exact h1
      simpa [Complex.norm_real, Real.norm_eq_abs] using this
    linarith
  rw [sshWinding_eq_circleIntegral]
  have : (∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z)) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      zero_le_one Set.countable_empty ?_ ?_
    · exact ContinuousOn.div continuousOn_const
        (Continuous.continuousOn (by fun_prop)) hne
    · intro z hz
      have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz.1
      exact DifferentiableAt.div (differentiableAt_const _)
        (by fun_prop) (hne z hz')
  rw [this, mul_zero]

/-- **SSH winding invariant.**  The SSH chain's topological phase is classified by an
integer winding number of the Bloch off-diagonal loop `k ↦ v + w e^{i k}`:
it equals `1` in the topological phase `|v| < w`, and `0` in the trivial phase
`w < |v|`; in particular it is always an integer whenever the bulk gap is open. -/
