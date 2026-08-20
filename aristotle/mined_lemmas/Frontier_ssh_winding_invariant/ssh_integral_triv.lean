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

lemma ssh_integral_triv (v w : ℂ) (h : ‖w‖ < ‖v‖) :
    (∮ z in C((0 : ℂ), 1), w / (v + w * z)) = 0 := by
  have hne : ∀ z ∈ closedBall (0 : ℂ) 1, v + w * z ≠ 0 := by
    intro z hz h0
    have hz1 : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_eq] using hz
    have hv : v = -(w * z) := by linear_combination h0
    have h1 : ‖v‖ = ‖w‖ * ‖z‖ := by
      rw [hv, norm_neg, norm_mul]
    have h2 : ‖w‖ * ‖z‖ ≤ ‖w‖ := by
      nlinarith [norm_nonneg w, norm_nonneg z]
    linarith
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one
    Set.countable_empty ?_ ?_
  · exact ContinuousOn.div continuousOn_const (by fun_prop) hne
  · intro z hz
    have hz' : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz.1
    exact (differentiableAt_const w).div (by fun_prop) (hne z hz')

/-- **SSH winding invariant.** The topological phase of the SSH model is classified by an
integer winding number of the Bloch off-diagonal element: it equals `1` in the topological
phase `‖v‖ < ‖w‖` and `0` in the trivial phase `‖w‖ < ‖v‖`. -/
