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

lemma ssh_integral_top (v w : ℂ) (h : ‖v‖ < ‖w‖) :
    (∮ z in C((0 : ℂ), 1), w / (v + w * z)) = 2 * Real.pi * Complex.I := by
  have hw : w ≠ 0 := by
    intro hw
    simp [hw] at h
    exact absurd h (not_lt.mpr (norm_nonneg v))
  have hfun : (fun z : ℂ => w / (v + w * z)) = fun z : ℂ => (z - (-(v / w)))⁻¹ := by
    funext z
    have hz : v + w * z = w * (z - (-(v / w))) := by
      field_simp; ring
    rw [hz]
    rcases eq_or_ne (z - (-(v / w))) 0 with h0 | h0
    · simp [h0]
    · field_simp
  rw [hfun]
  have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hmem : (-(v / w)) ∈ ball (0 : ℂ) 1 := by
    have : ‖v / w‖ < 1 := by
      rw [norm_div, div_lt_one hw0]
      exact h
    simpa [mem_ball, dist_eq, norm_neg] using this
  exact circleIntegral.integral_sub_inv_of_mem_ball hmem

/-- Key intermediate lemma (trivial case): when the intra-cell hopping dominates,
the integrand is holomorphic on the closed unit disk. -/
