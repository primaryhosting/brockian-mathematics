import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma det_fderiv_eq_zero_of_norm_eq_one {r : E → E} {x : E} {s : Set E} (hs : IsOpen s)
    (hx : x ∈ s) (hd : DifferentiableAt ℝ r x) (hn : ∀ y ∈ s, ‖r y‖ = 1) :
    (fderiv ℝ r x).det = 0 := by
  have hge : (fun y => ⟪r y, r y⟫) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [real_inner_self_eq_norm_sq, hn y hy]; norm_num
  have h0 : fderiv ℝ (fun y => ⟪r y, r y⟫) x = 0 := by rw [hge.fderiv_eq]; simp
  have hperp : ∀ y : E, ⟪r x, fderiv ℝ r x y⟫ = 0 := by
    intro y
    have h1 := fderiv_inner_apply (𝕜 := ℝ) hd hd y
    rw [h0] at h1
    simp only [ContinuousLinearMap.zero_apply] at h1
    have hc := real_inner_comm (r x) (fderiv ℝ r x y)
    linarith
  have hrx : ‖r x‖ = 1 := hn x hx
  rw [ContinuousLinearMap.det]
  by_contra hdet
  have hinj : Function.Injective ((fderiv ℝ r x : E →ₗ[ℝ] E)) := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) (r x)
  have h2 := hperp y
  rw [show fderiv ℝ r x y = r x from hy, real_inner_self_eq_norm_sq, hrx] at h2
  norm_num at h2

set_option maxHeartbeats 2000000 in
/-- **No retraction theorem** (`C¹` version): there is no continuously differentiable map from
a neighbourhood of the closed unit ball to the unit sphere which is the identity on the sphere. -/
