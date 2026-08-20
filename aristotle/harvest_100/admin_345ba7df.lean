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
noncomputable def sshBloch (v w : ℝ) (k : ℝ) : ℂ :=
  (v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)

/-- The winding number of the SSH model, i.e. the number of times the loop
`k ↦ h k = v + w e^{i k}` winds around the origin as `k` runs over the Brillouin zone
`[0, 2π]`:  `W = (1 / 2πi) ∫₀^{2π} h'(k) / h(k) dk`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    ∫ k in (0 : ℝ)..(2 * Real.pi), deriv (sshBloch v w) k / sshBloch v w k

/-- The SSH Bloch loop is exactly the circle of radius `w` centred at `v`. -/
lemma sshBloch_eq_circleMap (v w : ℝ) : sshBloch v w = circleMap (v : ℂ) w := rfl

/-- The winding number is `(2πi)⁻¹` times the contour integral of `1/z` over that circle. -/
lemma sshWinding_eq_circleIntegral (v w : ℝ) :
    sshWinding v w = (1 / (2 * (Real.pi : ℂ) * Complex.I)) * ∮ z in C((v : ℂ), w), z⁻¹ := by
  simp [sshWinding, circleIntegral, sshBloch_eq_circleMap, div_eq_mul_inv, smul_eq_mul]

lemma two_pi_I_ne_zero : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
  have : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  simp [this, Complex.I_ne_zero]

/-- **Topological phase.**  If the intercell hopping dominates (`|v| < w`) the winding number
equals `1`.  The key input is Mathlib's `circleIntegral.integral_sub_inv_of_mem_ball`
(the Cauchy integral `∮_{|z-c|=R} dz/(z-a) = 2πi` for `a` inside the circle). -/
theorem sshWinding_eq_one_of_abs_lt (v w : ℝ) (h : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ ball (v : ℂ) w := by
    have : dist (0 : ℂ) (v : ℂ) = |v| := by
      simp [Complex.dist_eq]
    simpa [Metric.mem_ball, this] using h
  have hI : (∮ z in C((v : ℂ), w), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    have := circleIntegral.integral_sub_inv_of_mem_ball hmem
    simpa using this
  rw [sshWinding_eq_circleIntegral, hI, one_div, inv_mul_cancel₀ two_pi_I_ne_zero]

/-- **Trivial phase.**  If the intracell hopping dominates (`w < |v|`, with `0 ≤ w`) the loop
does not enclose the origin and the winding number is `0`.  The key input is Mathlib's
Cauchy–Goursat theorem `DiffContOnCl.circleIntegral_eq_zero`. -/
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
theorem ssh_winding_invariant (v w : ℝ) (hw : 0 ≤ w) (hgap : |v| ≠ w) :
    (∃ n : ℤ, sshWinding v w = (n : ℂ)) ∧
      (|v| < w → sshWinding v w = 1) ∧ (w < |v| → sshWinding v w = 0) := by
  refine ⟨?_, fun h => sshWinding_eq_one_of_abs_lt v w h,
    fun h => sshWinding_eq_zero_of_lt_abs v w hw h⟩
  rcases lt_or_gt_of_ne hgap with h | h
  · exact ⟨1, by simpa using sshWinding_eq_one_of_abs_lt v w h⟩
  · exact ⟨0, by simpa using sshWinding_eq_zero_of_lt_abs v w hw h⟩

end Frontier

