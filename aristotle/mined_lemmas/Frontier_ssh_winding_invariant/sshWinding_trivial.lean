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
