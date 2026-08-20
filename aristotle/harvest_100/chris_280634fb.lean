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

/-- Off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger) chain,
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`. Chiral symmetry makes the Bloch Hamiltonian
`[[0, h(k)], [conj h(k), 0]]`, so the topology is entirely carried by `h`. -/
noncomputable def sshBloch (v w : ℂ) (k : ℝ) : ℂ := v + w * Complex.exp (k * Complex.I)

/-- The winding number of the SSH off-diagonal element around the origin,
`W = (2πi)⁻¹ ∫_0^{2π} h'(k)/h(k) dk`. -/
noncomputable def sshWinding (v w : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ k in (0:ℝ)..(2 * Real.pi), deriv (sshBloch v w) k / sshBloch v w k

/-- The derivative of the SSH Bloch function. -/
lemma hasDerivAt_sshBloch (v w : ℂ) (k : ℝ) :
    HasDerivAt (sshBloch v w) (w * Complex.I * Complex.exp (k * Complex.I)) k := by
  have h1 : HasDerivAt (fun k : ℝ => (k : ℂ) * Complex.I) Complex.I k := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := k)).mul_const Complex.I
  have h2 : HasDerivAt (fun k : ℝ => Complex.exp ((k : ℂ) * Complex.I))
      (Complex.exp ((k : ℂ) * Complex.I) * Complex.I) k := h1.cexp
  have h3 := (h2.const_mul w).const_add v
  have hfun : sshBloch v w = fun k : ℝ => v + w * Complex.exp ((k : ℂ) * Complex.I) := rfl
  rw [hfun]
  convert h3 using 1
  ring

lemma deriv_sshBloch (v w : ℂ) (k : ℝ) :
    deriv (sshBloch v w) k = w * Complex.I * Complex.exp (k * Complex.I) :=
  (hasDerivAt_sshBloch v w k).deriv

/-- **Key intermediate lemma.** The SSH winding integral is a contour integral over the
unit circle of the meromorphic function `z ↦ w / (v + w z)`. -/
lemma sshWinding_eq_circleIntegral (v w : ℂ) :
    sshWinding v w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C(0, 1), w / (v + w * z) := by
  unfold sshWinding
  congr 1
  rw [circleIntegral]
  refine intervalIntegral.integral_congr ?_
  intro k _
  simp only [deriv_circleMap, circleMap, smul_eq_mul, deriv_sshBloch, sshBloch,
    Complex.ofReal_one, one_mul, zero_add]
  ring

/-- Trivial phase: if the intracell hopping dominates (`‖w‖ < ‖v‖`), the winding number is `0`. -/
theorem sshWinding_eq_zero_of_norm_lt (v w : ℂ) (h : ‖w‖ < ‖v‖) :
    sshWinding v w = 0 := by
  have hne : ∀ z : ℂ, ‖z‖ ≤ 1 → v + w * z ≠ 0 := by
    intro z hz hzero
    have : ‖w * z‖ ≤ ‖w‖ := by
      rw [norm_mul]
      calc ‖w‖ * ‖z‖ ≤ ‖w‖ * 1 := by
            exact mul_le_mul_of_nonneg_left hz (norm_nonneg w)
        _ = ‖w‖ := mul_one _
    have hv : v = -(w * z) := by linear_combination hzero
    rw [hv, norm_neg] at h
    exact absurd h (not_lt.2 this)
  have hzero : ∮ z in C(0, 1), w / (v + w * z) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one
      Set.countable_empty ?_ ?_
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
      intro z hz
      exact hne z (by simpa [Complex.dist_eq] using hz)
    · intro z hz
      have hz' : ‖z‖ ≤ 1 := le_of_lt (by simpa [Complex.dist_eq] using hz.1)
      exact ((differentiableAt_const w).div
        ((differentiableAt_const v).add ((differentiableAt_const w).mul differentiableAt_id))
        (hne z hz'))
  rw [sshWinding_eq_circleIntegral, hzero, mul_zero]

/-- Topological phase: if the intercell hopping dominates (`‖v‖ < ‖w‖`),
the winding number is `1`. -/
theorem sshWinding_eq_one_of_norm_lt (v w : ℂ) (h : ‖v‖ < ‖w‖) :
    sshWinding v w = 1 := by
  have hw : w ≠ 0 := by
    intro hw0
    rw [hw0, norm_zero] at h
    exact absurd h (not_lt.2 (norm_nonneg v))
  have hcong : ∀ z : ℂ, w / (v + w * z) = (z - (-v / w))⁻¹ := by
    intro z
    have hz : z - (-v / w) = (v + w * z) / w := by
      field_simp
      ring
    rw [hz, inv_div]
  have hmem : (-v / w) ∈ Metric.ball (0 : ℂ) 1 := by
    simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, norm_div, norm_neg]
    rw [div_lt_one (by positivity)]
    exact h
  have : ∮ z in C(0, 1), w / (v + w * z) = 2 * (Real.pi : ℂ) * Complex.I := by
    rw [circleIntegral.integral_congr zero_le_one (fun z _ => hcong z)]
    exact circleIntegral.integral_sub_inv_of_mem_ball hmem
  rw [sshWinding_eq_circleIntegral, this, inv_mul_cancel₀]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- The winding number only depends on the SSH Bloch function up to a nonzero overall
rescaling of the two hopping amplitudes (the log-derivative integrand is scale invariant). -/
lemma sshWinding_scale (c v w : ℂ) (hc : c ≠ 0) :
    sshWinding (c * v) (c * w) = sshWinding v w := by
  unfold sshWinding
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro k _
  simp only [deriv_sshBloch, sshBloch]
  have hnum : c * w * Complex.I * Complex.exp ((k : ℂ) * Complex.I)
      = c * (w * Complex.I * Complex.exp ((k : ℂ) * Complex.I)) := by ring
  have hden : c * v + c * w * Complex.exp ((k : ℂ) * Complex.I)
      = c * (v + w * Complex.exp ((k : ℂ) * Complex.I)) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hc]

/-- **SSH winding invariant.** The topological phase of the SSH model is classified by an
integer winding number of the off-diagonal Bloch function `h(k) = v + w e^{ik}`:
it vanishes in the trivial phase `‖w‖ < ‖v‖` and equals one in the topological
phase `‖v‖ < ‖w‖`. In particular the winding number is always an integer, and it jumps
only at the gap-closing point `‖v‖ = ‖w‖`. -/
theorem ssh_winding_invariant (v w : ℂ) :
    (‖w‖ < ‖v‖ → sshWinding v w = 0) ∧ (‖v‖ < ‖w‖ → sshWinding v w = 1) ∧
      (‖w‖ ≠ ‖v‖ → ∃ n : ℤ, sshWinding v w = (n : ℂ)) := by
  refine ⟨sshWinding_eq_zero_of_norm_lt v w, sshWinding_eq_one_of_norm_lt v w, ?_⟩
  intro hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨0, by rw [sshWinding_eq_zero_of_norm_lt v w hlt]; norm_num⟩
  · exact ⟨1, by rw [sshWinding_eq_one_of_norm_lt v w hgt]; norm_num⟩

end Frontier

