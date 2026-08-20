import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

theorem exists_fixedPoint_of_contDiff {g : E → E} (hg : ContDiff ℝ 1 g)
    (hmaps : ∀ x ∈ closedBall (0 : E) 1, ‖g x‖ ≤ 1) :
    ∃ x ∈ closedBall (0 : E) 1, g x = x := by
  by_contra hcon
  push_neg at hcon
  set u : E → E := fun x => x - g x with hudef
  have hucd : ContDiff ℝ 1 u := contDiff_id.sub hg
  set A : E → ℝ := fun x => ⟪x, u x⟫ with hAdef
  set D : E → ℝ := fun x => A x ^ 2 + ‖u x‖ ^ 2 * (1 - ‖x‖ ^ 2) with hDdef
  have hAcd : ContDiff ℝ 1 A := contDiff_id.inner ℝ hucd
  have hDcd : ContDiff ℝ 1 D :=
    (hAcd.pow 2).add ((hucd.norm_sq ℝ).mul (contDiff_const.sub (contDiff_id.norm_sq ℝ)))
  set S : E → ℝ := fun x => (-A x + Real.sqrt (D x)) / ‖u x‖ ^ 2 with hSdef
  set r : E → E := fun x => x + S x • u x with hrdef
  set U : Set E := {x | u x ≠ 0 ∧ 0 < D x} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_ne_fun hucd.continuous continuous_const).inter
      (isOpen_lt continuous_const hDcd.continuous)
  have hApos : ∀ x ∈ sphere (0 : E) 1, 0 < A x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by simpa using hx
    by_contra hle
    push_neg at hle
    have hAx : A x = ‖x‖ ^ 2 - ⟪x, g x⟫ := by
      rw [hAdef]; simp [hudef, inner_sub_right]
    rw [hAx, hx1] at hle
    have hgx : ‖g x‖ ≤ 1 := hmaps x (by simp [hx1])
    have hz : ‖g x - x‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, hx1]
      nlinarith [real_inner_comm x (g x), norm_nonneg (g x)]
    have h0 : ‖g x - x‖ = 0 := by nlinarith [norm_nonneg (g x - x)]
    exact hcon x (by simp [hx1]) (sub_eq_zero.mp (norm_eq_zero.mp h0))
  have hsub : closedBall (0 : E) 1 ⊆ U := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    have hune : u x ≠ 0 := fun h => hcon x hx (sub_eq_zero.mp h).symm
    refine ⟨hune, ?_⟩
    show 0 < A x ^ 2 + ‖u x‖ ^ 2 * (1 - ‖x‖ ^ 2)
    rcases lt_or_eq_of_le hx1 with h | h
    · have h1 : 0 < ‖u x‖ ^ 2 := by positivity
      have h2 : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      nlinarith [sq_nonneg (A x)]
    · have h0 : (1 : ℝ) - ‖x‖ ^ 2 = 0 := by rw [h]; norm_num
      rw [h0, mul_zero, add_zero]
      exact pow_pos (hApos x (mem_sphere_zero_iff_norm.mpr h)) 2
  have hrcd : ContDiffOn ℝ 1 r U := by
    intro x hx
    have hsqrt : ContDiffAt ℝ 1 (fun y => Real.sqrt (D y)) x :=
      (Real.contDiffAt_sqrt (ne_of_gt hx.2)).comp x hDcd.contDiffAt
    have hnu : ‖u x‖ ^ 2 ≠ 0 := by
      have : u x ≠ 0 := hx.1
      positivity
    have hScd : ContDiffAt ℝ 1 S x :=
      ContDiffAt.div (hAcd.contDiffAt.neg.add hsqrt) (hucd.norm_sq ℝ).contDiffAt hnu
    exact (contDiffAt_id.add (hScd.smul hucd.contDiffAt)).contDiffWithinAt
  have hnorm : ∀ x ∈ closedBall (0 : E) 1, ‖r x‖ = 1 := fun x hx =>
    norm_ray_eq_one (hsub hx).2.le (hsub hx).1
  have hfix : ∀ x ∈ sphere (0 : E) 1, r x = x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by simpa using hx
    have hS0 : S x = 0 := ray_coeff_eq_zero hx1 (hApos x hx)
    show x + S x • u x = x
    rw [hS0, zero_smul, add_zero]
  exact no_smooth_retraction hUopen hsub hrcd hnorm hfix

/-- **Brouwer's fixed point theorem** for the closed unit ball of a finite dimensional real
inner product space. -/
