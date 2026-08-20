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
noncomputable def sshBloch (v w : ℂ) : ℂ → ℂ := fun z => v + w * z

/-- The winding number of the SSH Bloch off-diagonal element around the origin,
defined by the argument principle as the contour integral of `h'/h` over the
Brillouin-zone circle `|z| = 1`. -/
noncomputable def sshWinding (v w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C((0 : ℂ), 1), deriv (sshBloch v w) z / sshBloch v w z

lemma sshBloch_deriv (v w : ℂ) : deriv (sshBloch v w) = fun _ => w := by
  funext z
  have h0 : HasDerivAt (fun x : ℂ => v + w * x) (w * 1) z :=
    ((hasDerivAt_id z).const_mul w).const_add v
  rw [mul_one] at h0
  exact h0.deriv

lemma sshWinding_eq (v w : ℂ) :
    sshWinding v w = (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C((0 : ℂ), 1), w / (v + w * z) := by
  simp [sshWinding, sshBloch_deriv, sshBloch]

lemma two_pi_I_ne_zero : (2 * Real.pi * Complex.I) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero]

/-- Key intermediate lemma (topological case): when the inter-cell hopping dominates,
the integrand is the Cauchy kernel of a pole inside the unit disk. -/
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
theorem ssh_winding_invariant (v w : ℂ) :
    (‖v‖ < ‖w‖ → sshWinding v w = 1) ∧ (‖w‖ < ‖v‖ → sshWinding v w = 0) := by
  constructor
  · intro h
    rw [sshWinding_eq, ssh_integral_top v w h, inv_mul_cancel₀ two_pi_I_ne_zero]
  · intro h
    rw [sshWinding_eq, ssh_integral_triv v w h, mul_zero]

/-- Away from `‖v‖ = ‖w‖` the SSH chain is gapped: the Bloch off-diagonal element
`v + w e^{i k}` never vanishes on the Brillouin zone, so the winding number is well posed. -/
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
theorem ssh_winding_mem_int (v w : ℂ) (hgap : ‖v‖ ≠ ‖w‖) : ∃ n : ℤ, sshWinding v w = n := by
  rcases lt_or_gt_of_ne hgap with hlt | hgt
  · exact ⟨1, by simpa using (ssh_winding_invariant v w).1 hlt⟩
  · exact ⟨0, by simpa using (ssh_winding_invariant v w).2 hgt⟩

end Frontier

