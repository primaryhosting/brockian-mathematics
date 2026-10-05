/-
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Complex intervalIntegral

/-- Off-diagonal entry of the Bloch Hamiltonian of the Su–Schrieffer–Heeger (SSH) chain,
`h(k) = v + w e^{ik}`, where `v` is the intracell and `w` the intercell hopping amplitude. -/
noncomputable def sshBloch (v w : ℝ) (k : ℝ) : ℂ :=
  (v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)

/-- The winding number of the SSH Bloch Hamiltonian around the origin,
`(2πi)⁻¹ ∫₀^{2π} h'(k)/h(k) dk`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    ∫ k in (0:ℝ)..(2 * Real.pi), deriv (sshBloch v w) k / sshBloch v w k

lemma hasDerivAt_sshBloch (v w : ℝ) (k : ℝ) :
    HasDerivAt (sshBloch v w) ((w : ℂ) * Complex.I * Complex.exp (k * Complex.I)) k := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 k := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := k))
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I k := by
    simpa using h1.mul_const Complex.I
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((k : ℂ) * Complex.I) * Complex.I) k := h2.cexp
  have h4 := (h3.const_mul (w : ℂ)).const_add (v : ℂ)
  refine h4.congr_deriv ?_
  ring

lemma deriv_sshBloch (v w : ℝ) (k : ℝ) :
    deriv (sshBloch v w) k = (w : ℂ) * Complex.I * Complex.exp (k * Complex.I) :=
  (hasDerivAt_sshBloch v w k).deriv

/-- The winding integral of the SSH model is a circle integral of `(z + v)⁻¹`
over the circle of radius `w` centred at the origin. -/
lemma sshWinding_eq (v w : ℝ) :
    sshWinding v w =
      (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(0, w), (z - (-(v : ℂ)))⁻¹ := by
  unfold sshWinding
  congr 1
  rw [circleIntegral]
  refine intervalIntegral.integral_congr ?_
  intro k _
  simp only [deriv_circleMap, circleMap, deriv_sshBloch, sshBloch, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring_nf

theorem ssh_winding_invariant (v w : ℝ) (hw : 0 < w) (hne : |v| ≠ w) :
    sshWinding v w = if |v| < w then 1 else 0 := by
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [sshWinding_eq]
  by_cases hlt : |v| < w
  · rw [if_pos hlt]
    have hmem : (-(v : ℂ)) ∈ Metric.ball (0 : ℂ) w := by
      simp only [Metric.mem_ball, dist_zero_right, norm_neg]
      simpa using hlt
    rw [circleIntegral.integral_sub_inv_of_mem_ball hmem]
    field_simp
  · rw [if_neg hlt]
    have hgt : w < |v| := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
    have hout : ∀ z ∈ Metric.closedBall (0 : ℂ) w, z - (-(v : ℂ)) ≠ 0 := by
      intro z hz hz0
      have hzv : z = -(v : ℂ) := by
        have := sub_eq_zero.mp hz0
        exact this
      rw [hzv] at hz
      simp only [Metric.mem_closedBall, dist_zero_right, norm_neg] at hz
      have : |v| ≤ w := by simpa using hz
      exact absurd this (not_le.mpr hgt)
    have hdiff : DifferentiableOn ℂ (fun z : ℂ => (z - (-(v : ℂ)))⁻¹)
        (Metric.closedBall (0 : ℂ) w) := by
      intro z hz
      exact (((differentiableAt_id.sub_const (-(v : ℂ))).inv
        (hout z hz)).differentiableWithinAt)
    have hcl : closure (Metric.ball (0 : ℂ) w) = Metric.closedBall (0 : ℂ) w :=
      closure_ball (0 : ℂ) (ne_of_gt hw)
    have hdc : DiffContOnCl ℂ (fun z : ℂ => (z - (-(v : ℂ)))⁻¹) (Metric.ball (0 : ℂ) w) := by
      constructor
      · exact hdiff.mono (fun z hz => Metric.ball_subset_closedBall hz)
      · rw [hcl]
        exact hdiff.continuousOn
    rw [hdc.circleIntegral_eq_zero hw.le, mul_zero]

#print axioms Frontier.ssh_winding_invariant

end Frontier

