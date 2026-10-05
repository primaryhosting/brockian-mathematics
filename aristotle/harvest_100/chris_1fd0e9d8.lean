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
noncomputable def sshH (v w : ℝ) (k : ℝ) : ℂ := (v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)

/-- The winding number of the SSH model: the number of times the loop
`k ↦ h(k)`, `k ∈ [0, 2π]`, winds around the origin, computed as
`(2π i)⁻¹ ∫₀^{2π} h'(k) / h(k) dk`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ k in (0 : ℝ)..(2 * Real.pi),
      (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) / sshH v w k

/-- The winding integral of the SSH model, rewritten as a contour integral over the unit
circle. -/
lemma sshWinding_eq_circleIntegral (v w : ℝ) :
    sshWinding v w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z) := by
  unfold sshWinding circleIntegral
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro k _
  simp only [deriv_circleMap, circleMap, sshH, smul_eq_mul]
  push_cast
  ring

/-- In the topological phase `|v| < w` the SSH winding number equals `1`. -/
theorem sshWinding_eq_one (v w : ℝ) (hw : 0 < w) (hvw : |v| < w) :
    sshWinding v w = 1 := by
  have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hmem : (-(v / w) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    have : ‖(-(v / w) : ℂ)‖ < 1 := by
      have : ‖(-(v / w) : ℂ)‖ = |v| / w := by
        rw [norm_neg]
        rw [show ((v : ℂ) / (w : ℂ)) = ((v / w : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hw]
      rw [this]
      exact (div_lt_one hw).2 hvw
    simpa [Metric.mem_ball, dist_eq_norm] using this
  have hfun : ∀ z : ℂ, (w : ℂ) / ((v : ℂ) + (w : ℂ) * z) = (z - (-(v / w) : ℂ))⁻¹ := by
    intro z
    rw [sub_neg_eq_add]
    rw [eq_comm, inv_eq_iff_eq_inv, eq_comm, inv_div]
    field_simp
    ring
  rw [sshWinding_eq_circleIntegral]
  simp only [hfun]
  rw [circleIntegral.integral_sub_inv_of_mem_ball hmem]
  field_simp

/-- In the trivial phase `w < |v|` the SSH winding number equals `0`. -/
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
theorem ssh_winding_invariant :
    (∀ v w : ℝ, 0 < w → |v| < w → sshWinding v w = 1) ∧
    (∀ v w : ℝ, 0 < w → w < |v| → sshWinding v w = 0) ∧
    (∀ v w : ℝ, 0 < w → |v| ≠ w → ∃ n : ℤ, sshWinding v w = (n : ℂ)) := by
  refine ⟨sshWinding_eq_one, sshWinding_eq_zero, ?_⟩
  intro v w hw hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨1, by rw [sshWinding_eq_one v w hw h]; norm_num⟩
  · exact ⟨0, by rw [sshWinding_eq_zero v w hw h]; norm_num⟩

end Frontier

