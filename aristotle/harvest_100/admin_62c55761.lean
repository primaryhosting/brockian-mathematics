import Mathlib
/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Metric Set
open scoped Real Topology

namespace Frontier

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger) chain
with intracell hopping `v` and intercell hopping `w`:
`h v w k = v + w * exp (I * k)`. -/
noncomputable def sshOffDiag (v w : ℝ) (k : ℝ) : ℂ := (v : ℂ) + (w : ℂ) * Complex.exp (Complex.I * k)

/-- The winding number of the SSH model, defined as the winding number of the loop
`k ↦ sshOffDiag v w k` around the origin, i.e. the contour integral
`(2πi)⁻¹ ∮_{|z - v| = w} dz / z`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * ↑π * Complex.I)⁻¹ * ∮ z in C((v : ℂ), w), z⁻¹

/-- The contour-integral definition of the winding number agrees with the usual physics formula
`(2πi)⁻¹ ∫₀^{2π} h'(k) / h(k) dk` for the SSH loop `h k = v + w e^{ik}`. -/
theorem sshWinding_eq_phase_integral (v w : ℝ) :
    sshWinding v w =
      (2 * ↑π * Complex.I)⁻¹ *
        ∫ k in (0 : ℝ)..(2 * π), (Complex.I * w * Complex.exp (Complex.I * k)) / sshOffDiag v w k := by
  unfold sshWinding sshOffDiag circleIntegral
  congr 1
  refine intervalIntegral.integral_congr fun k _ => ?_
  simp only [deriv_circleMap, circleMap, smul_eq_mul, div_eq_mul_inv]
  ring_nf

/-- **The gap condition.** The SSH loop `k ↦ v + w e^{ik}` misses the origin (equivalently, the
Bloch Hamiltonian is gapped) exactly when `|v| ≠ w`. -/
theorem sshOffDiag_ne_zero_iff (v w : ℝ) (hw : 0 ≤ w) :
    (∀ k : ℝ, sshOffDiag v w k ≠ 0) ↔ |v| ≠ w := by
  constructor
  · intro h hv
    rcases eq_or_lt_of_le hw with hw0 | hw0
    · have hv0 : v = 0 := by
        have hva : |v| = 0 := by rw [hv, ← hw0]
        exact abs_eq_zero.mp hva
      exact h 0 (by simp [sshOffDiag, hv0, ← hw0])
    · rcases (abs_eq (le_of_lt hw0)).mp hv with hvw | hvw
      · refine h π ?_
        simp only [sshOffDiag, hvw]
        rw [show (Complex.I * ((π : ℝ) : ℂ)) = (π : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]
        ring
      · refine h 0 ?_
        simp [sshOffDiag, hvw]
  · intro hv k hk
    apply hv
    have hvz : (v : ℂ) = -((w : ℂ) * Complex.exp (Complex.I * k)) := by
      have h0 : (v : ℂ) + (w : ℂ) * Complex.exp (Complex.I * k) = 0 := hk
      linear_combination h0
    have hnorm : ‖(v : ℂ)‖ = ‖(w : ℂ) * Complex.exp (Complex.I * k)‖ := by rw [hvz, norm_neg]
    simpa [Complex.norm_exp, abs_of_nonneg hw] using hnorm

/-- Away from the origin the map `z ↦ z⁻¹` is holomorphic; on a closed disc missing the origin
this gives the hypotheses needed for Cauchy's theorem. -/
theorem ne_zero_of_mem_closedBall {v w : ℝ} (hgap : w < |v|) {z : ℂ}
    (hz : z ∈ closedBall (v : ℂ) w) : z ≠ 0 := by
  have hd : ‖z - (v : ℂ)‖ ≤ w := by
    simpa [Complex.dist_eq] using (mem_closedBall.mp hz)
  have hv : ‖(v : ℂ)‖ = |v| := by simp
  have : |v| - ‖z - (v : ℂ)‖ ≤ ‖z‖ := by
    have := norm_sub_norm_le (v : ℂ) (v - z)
    have h2 : ‖(v : ℂ) - ((v : ℂ) - z)‖ = ‖z‖ := by ring_nf
    have h3 : ‖(v : ℂ) - z‖ = ‖z - (v : ℂ)‖ := norm_sub_rev _ _
    rw [h2, h3, hv] at this
    exact this
  have hpos : 0 < ‖z‖ := lt_of_lt_of_le (by linarith) this
  simpa using norm_pos_iff.mp hpos

/-- **Trivial phase.** If the intracell hopping dominates (`w < |v|`) the origin lies outside the
loop and the winding number vanishes. -/
theorem sshWinding_trivial {v w : ℝ} (hw : 0 ≤ w) (hgap : w < |v|) : sshWinding v w = 0 := by
  have hzero : (∮ z in C((v : ℂ), w), z⁻¹) = 0 := by
    refine DiffContOnCl.circleIntegral_eq_zero hw ?_
    constructor
    · intro z hz
      have hz0 : z ≠ 0 := ne_zero_of_mem_closedBall hgap (ball_subset_closedBall hz)
      exact ((differentiableAt_inv_iff.mpr hz0).differentiableWithinAt)
    · intro z hz
      have hz0 : z ≠ 0 :=
        ne_zero_of_mem_closedBall hgap (closure_ball_subset_closedBall hz)
      exact ((differentiableAt_inv_iff.mpr hz0).continuousAt).continuousWithinAt
  simp [sshWinding, hzero]

/-- **Topological phase.** If the intercell hopping dominates (`|v| < w`) the origin lies inside the
loop and the winding number equals `1`. -/
theorem sshWinding_topological {v w : ℝ} (hgap : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ ball (v : ℂ) w := by
    simp [Complex.dist_eq, mem_ball, hgap]
  have hint : (∮ z in C((v : ℂ), w), z⁻¹) = 2 * ↑π * Complex.I := by
    have := circleIntegral.integral_sub_inv_of_mem_ball hmem
    simpa using this
  have hne : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero]
  rw [sshWinding, hint, inv_mul_cancel₀ hne]

/-- **The SSH winding invariant.**

For the SSH chain with hoppings `v` (intracell) and `w ≥ 0` (intercell), the winding number of the
Bloch off-diagonal loop `k ↦ v + w e^{ik}` around the origin is:

* an *integer* whenever the spectrum is gapped (`|v| ≠ w`);
* equal to `1` in the topological phase `|v| < w`;
* equal to `0` in the trivial phase `w < |v|`;
* *invariant* under any change of the parameters that stays inside one and the same phase.

Thus the topological phase of the SSH model is classified by a `ℤ`-valued invariant. -/
theorem ssh_winding_invariant (v w : ℝ) (hw : 0 ≤ w) :
    (|v| ≠ w → ∃ n : ℤ, sshWinding v w = (n : ℂ)) ∧
    (|v| < w → sshWinding v w = 1) ∧
    (w < |v| → sshWinding v w = 0) ∧
    (∀ v' w' : ℝ, 0 ≤ w' →
      ((|v| < w ∧ |v'| < w') ∨ (w < |v| ∧ w' < |v'|)) →
        sshWinding v w = sshWinding v' w') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨1, by simpa using sshWinding_topological h⟩
    · exact ⟨0, by simpa using sshWinding_trivial hw h⟩
  · exact fun h => sshWinding_topological h
  · exact fun h => sshWinding_trivial hw h
  · rintro v' w' hw' (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [sshWinding_topological h1, sshWinding_topological h2]
    · rw [sshWinding_trivial hw h1, sshWinding_trivial hw' h2]

end Frontier

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

