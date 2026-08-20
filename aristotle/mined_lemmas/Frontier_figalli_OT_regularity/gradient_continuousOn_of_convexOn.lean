/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖²/2`. -/

theorem gradient_continuousOn_of_convexOn {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω)
    (hu : ConvexOn ℝ Ω u) (hdiff : ∀ x ∈ Ω, DifferentiableAt ℝ u x) :
    ContinuousOn (fun x => gradient u x) Ω := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  set q : E := gradient u x with hq
  have hgrad : HasGradientAt u q x := (hdiff x hx).hasGradientAt
  have hlo : (fun z => u z - u x - ⟪q, z - x⟫_ℝ) =o[nhds x] (fun z => z - x) := by
    have := hgrad.hasFDerivAt.isLittleO
    simpa [real_inner_comm] using this
  have hc : (0 : ℝ) < ε / 4 := by linarith
  have hev := hlo.def hc
  rw [Metric.eventually_nhds_iff_ball] at hev
  obtain ⟨r₀, hr₀, hball⟩ := hev
  obtain ⟨r₁, hr₁, hsub⟩ := Metric.isOpen_iff.mp hΩ x hx
  set r := min r₀ r₁ with hr
  have hrpos : 0 < r := lt_min hr₀ hr₁
  have hest : ∀ w : E, ‖w - x‖ < r → |u w - u x - ⟪q, w - x⟫_ℝ| ≤ (ε / 4) * ‖w - x‖ := by
    intro w hw
    have hw' : w ∈ Metric.ball x r₀ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hw (min_le_left _ _)
    simpa using hball w hw'
  have hmemΩ : ∀ w : E, ‖w - x‖ < r → w ∈ Ω := by
    intro w hw
    refine hsub ?_
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hw (min_le_right _ _)
  refine ⟨r / 4, by linarith, ?_⟩
  intro y hy
  rw [dist_eq_norm] at hy ⊢
  set p : E := gradient u y with hp
  by_cases hpq : p = q
  · simp [hpq, hε]
  · have hnorm : 0 < ‖p - q‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero_of_ne hpq
    set t : ℝ := r / 2 with ht
    set e : E := (‖p - q‖)⁻¹ • (p - q) with he
    set z : E := y + t • e with hz
    have hyx : ‖y - x‖ < r / 4 := hy
    have hnorme : ‖e‖ = 1 := by
      rw [he, norm_smul]
      simp [inv_mul_cancel₀ (ne_of_gt hnorm)]
    have hzx : ‖z - x‖ < r := by
      have hzx' : z - x = (y - x) + t • e := by rw [hz]; abel
      rw [hzx']
      calc ‖(y - x) + t • e‖ ≤ ‖y - x‖ + ‖t • e‖ := norm_add_le _ _
        _ = ‖y - x‖ + t := by
            rw [norm_smul, hnorme, Real.norm_eq_abs, abs_of_pos (by positivity)]; ring
        _ < r / 4 + r / 2 := by linarith
        _ < r := by linarith
    have hyΩ : y ∈ Ω := hmemΩ y (by linarith)
    have hzΩ : z ∈ Ω := hmemΩ z hzx
    have hsg : ⟪p, z - y⟫_ℝ ≤ u z - u y := inner_gradient_le_sub hu hyΩ hzΩ (hdiff y hyΩ)
    have hzy : z - y = t • e := by rw [hz]; abel
    have hinner_pe : ⟪p - q, e⟫_ℝ = ‖p - q‖ := by
      rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hA := hest z hzx
    have hB := hest y (by linarith)
    have hexp : u z - u y - ⟪q, z - y⟫_ℝ
        = (u z - u x - ⟪q, z - x⟫_ℝ) - (u y - u x - ⟪q, y - x⟫_ℝ) := by
      have hqz : ⟪q, z - x⟫_ℝ - ⟪q, y - x⟫_ℝ = ⟪q, z - y⟫_ℝ := by
        rw [← inner_sub_right]; congr 1; abel
      linarith [hqz]
    have hkey : t * ‖p - q‖ ≤ (ε / 4) * ‖z - x‖ + (ε / 4) * ‖y - x‖ := by
      have h1 : ⟪p, z - y⟫_ℝ - ⟪q, z - y⟫_ℝ = t * ‖p - q‖ := by
        rw [hzy, ← inner_sub_left, real_inner_smul_right, hinner_pe]
      have h2 : t * ‖p - q‖ ≤ u z - u y - ⟪q, z - y⟫_ℝ := by linarith [hsg, h1]
      rw [hexp] at h2
      linarith [(abs_le.mp hA).1, (abs_le.mp hA).2, (abs_le.mp hB).1, (abs_le.mp hB).2]
    have hbnd : (r / 2) * ‖p - q‖ ≤ (ε / 4) * r + (ε / 4) * (r / 4) := by
      have hzx' : ‖z - x‖ ≤ r := le_of_lt hzx
      have hyx' : ‖y - x‖ ≤ r / 4 := le_of_lt hyx
      have : (ε / 4) * ‖z - x‖ + (ε / 4) * ‖y - x‖ ≤ (ε / 4) * r + (ε / 4) * (r / 4) := by
        nlinarith [norm_nonneg (z - x), norm_nonneg (y - x)]
      rw [ht] at hkey
      linarith
    have h5 : ‖p - q‖ ≤ 5 * ε / 8 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    linarith

/-- **Figalli's optimal transport regularity, flat (MTW ≡ 0) base case.**

For the quadratic cost `c(x,y) = ‖x-y‖²/2` on a real Hilbert space — the model case in which the
Ma–Trudinger–Wang condition holds with constant `0` — let `u` be a convex potential on an open
domain `Ω`, differentiable there.  Then

* the Brenier map `T = ∇u` is optimal: its graph is `c`-cyclically monotone, and
* `T` is continuous on `Ω`, i.e. the optimal transport map is regular. -/
