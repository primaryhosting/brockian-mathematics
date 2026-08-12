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

/-!
# The SSH model: quantization of the winding number

The Su–Schrieffer–Heeger (SSH) chain has Bloch Hamiltonian
`H(k) = Re h(k) σₓ + Im h(k) σ_y` with off-diagonal (chiral) component

  `h(k) = v + w e^{ik}`,

where `v` is the intracell and `w` the intercell hopping amplitude.  As long as the
spectrum is gapped (`h(k) ≠ 0` for all `k`, which happens exactly when `|v| ≠ |w|`) the
phase is classified by the winding number of the loop `k ↦ h(k)` around the origin,

  `W = (2πi)⁻¹ ∫₀^{2π} h'(k) / h(k) dk`.

We prove that `W` is an integer, equal to `1` in the topological regime `|v| < |w|` and to
`0` in the trivial regime `|w| < |v|`.
-/

namespace Frontier

open Complex Metric

/-- Off-diagonal (chiral) component `h(k) = v + w e^{i k}` of the SSH Bloch Hamiltonian. -/
noncomputable def sshBloch (v w : ℝ) (k : ℝ) : ℂ :=
  (v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)

/-- The winding number of the SSH loop `k ↦ h(k)` around the origin,
`W = (2πi)⁻¹ ∫₀^{2π} h'(k)/h(k) dk`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ k in (0 : ℝ)..(2 * Real.pi), deriv (sshBloch v w) k / sshBloch v w k

lemma hasDerivAt_sshBloch (v w : ℝ) (k : ℝ) :
    HasDerivAt (sshBloch v w) ((w : ℂ) * Complex.I * Complex.exp (k * Complex.I)) k := by
  have h1 : HasDerivAt (fun k : ℝ => (k : ℂ) * Complex.I) Complex.I k := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := k)).mul_const Complex.I
  have h3 := (h1.cexp.const_mul (w : ℂ)).const_add (v : ℂ)
  convert h3 using 1
  ring

lemma deriv_sshBloch (v w : ℝ) (k : ℝ) :
    deriv (sshBloch v w) k = (w : ℂ) * Complex.I * Complex.exp (k * Complex.I) :=
  (hasDerivAt_sshBloch v w k).deriv

/-- The defining integral of the winding number is a contour integral over the unit circle. -/
lemma sshWinding_eq_circleIntegral (v w : ℝ) :
    sshWinding v w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z) := by
  have hcirc : (∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z))
      = ∫ k in (0 : ℝ)..(2 * Real.pi),
          (Complex.exp (k * Complex.I) * Complex.I) •
            ((w : ℂ) / ((v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I))) := by
    rw [circleIntegral]
    simp [deriv_circleMap, circleMap]
  rw [sshWinding, hcirc]
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro k _
  simp only [deriv_sshBloch, sshBloch, smul_eq_mul]
  ring

/-- Trivial phase: if `|w| < |v|` the winding number vanishes. -/
theorem sshWinding_trivial (v w : ℝ) (h : |w| < |v|) : sshWinding v w = 0 := by
  have hne : ∀ z : ℂ, ‖z‖ ≤ 1 → (v : ℂ) + (w : ℂ) * z ≠ 0 := by
    intro z hz hcon
    have h1 : (w : ℂ) * z = -(v : ℂ) := by linear_combination hcon
    have h2 : ‖(w : ℂ) * z‖ = ‖(v : ℂ)‖ := by rw [h1, norm_neg]
    rw [norm_mul] at h2
    have h3 : ‖(w : ℂ)‖ * ‖z‖ ≤ ‖(w : ℂ)‖ := by
      nlinarith [norm_nonneg z, norm_nonneg (w : ℂ)]
    simp only [Complex.norm_real, Real.norm_eq_abs] at h2 h3
    linarith
  have hzero : (∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z)) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable (by norm_num)
      Set.countable_empty ?_ ?_
    · apply ContinuousOn.div continuousOn_const
        ((continuousOn_const).add (continuousOn_const.mul continuousOn_id))
      intro z hz
      refine hne z ?_
      simpa [Complex.dist_eq] using (mem_closedBall.1 hz)
    · intro z hz
      refine DifferentiableAt.div (differentiableAt_const _)
        ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)) ?_
      refine hne z ?_
      have := mem_ball.1 hz.1
      simp only [Complex.dist_eq, sub_zero] at this
      exact this.le
  rw [sshWinding_eq_circleIntegral, hzero, mul_zero]

/-- Topological phase: if `|v| < |w|` the winding number equals `1`. -/
theorem sshWinding_topological (v w : ℝ) (h : |v| < |w|) : sshWinding v w = 1 := by
  have hw : (w : ℂ) ≠ 0 := by
    have : w ≠ 0 := by
      intro h0; rw [h0] at h; simp at h; exact absurd h (not_lt.2 (abs_nonneg v))
    exact_mod_cast this
  have hpt : (-((v : ℂ) / (w : ℂ))) ∈ ball (0 : ℂ) 1 := by
    have hwn : ‖(w : ℂ)‖ ≠ 0 := by simpa using hw
    have : ‖(v : ℂ) / (w : ℂ)‖ < 1 := by
      rw [norm_div, div_lt_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hwn))]
      simpa [Complex.norm_real, Real.norm_eq_abs] using h
    simpa [Complex.dist_eq] using this
  have hint : (∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z))
      = 2 * (Real.pi : ℂ) * Complex.I := by
    have key : ∀ z : ℂ, (w : ℂ) / ((v : ℂ) + (w : ℂ) * z) = (z - (-((v : ℂ) / (w : ℂ))))⁻¹ := by
      intro z
      have hfac : (v : ℂ) + (w : ℂ) * z = (w : ℂ) * (z + (v : ℂ) / (w : ℂ)) := by
        field_simp; ring
      rw [sub_neg_eq_add, hfac, ← div_div, div_self hw, one_div]
    simp only [key]
    exact circleIntegral.integral_sub_inv_of_mem_ball hpt
  rw [sshWinding_eq_circleIntegral, hint]
  exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero])

/-- **The SSH topological invariant.**  Whenever the SSH chain is gapped (`|v| ≠ |w|`), its
winding number `W = (2πi)⁻¹ ∫₀^{2π} h'(k)/h(k) dk`, with `h(k) = v + w e^{ik}`, is an integer:
it equals `1` in the topological regime `|v| < |w|` and `0` in the trivial regime `|w| < |v|`. -/
theorem ssh_winding_invariant (v w : ℝ) (hgap : |v| ≠ |w|) :
    ∃ n : ℤ, sshWinding v w = (n : ℂ) ∧ n = if |v| < |w| then 1 else 0 := by
  rcases lt_or_gt_of_ne hgap with h | h
  · exact ⟨1, by simpa using sshWinding_topological v w h, by simp [h]⟩
  · exact ⟨0, by simpa using sshWinding_trivial v w h, by simp [not_lt.2 h.le]⟩

end Frontier

