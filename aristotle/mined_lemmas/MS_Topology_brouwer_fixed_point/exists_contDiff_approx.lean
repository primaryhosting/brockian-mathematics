import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

lemma exists_contDiff_approx {K : Set E} (hK : IsCompact K) (φ : E → E)
    (hφ : ContinuousOn φ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E → E, ContDiff ℝ 1 G ∧ ∀ x ∈ K, ‖G x - φ x‖ < ε := by
  classical
  set d := finrank ℝ E with hd
  set bb := stdOrthonormalBasis ℝ E with hbb
  set ε' : ℝ := ε / (d + 1) with hε'
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  have hcoord : ∀ i : Fin d, ∃ Gi : E → ℝ, ContDiff ℝ 1 Gi ∧
      ∀ x ∈ K, |Gi x - ⟪bb i, φ x⟫| < ε' := fun i =>
    exists_contDiff_approx_real hK (fun v => ⟪bb i, φ v⟫) (continuousOn_const.inner hφ) hε'pos
  choose G hG1 hG2 using hcoord
  refine ⟨fun v => ∑ i, G i v • bb i, ContDiff.sum fun i _ => (hG1 i).smul contDiff_const, ?_⟩
  intro x hx
  have hrep : φ x = ∑ i, ⟪bb i, φ x⟫ • bb i := by
    conv_lhs => rw [← bb.sum_repr (φ x)]
    exact Finset.sum_congr rfl fun i _ => by rw [bb.repr_apply_apply]
  have hdiff : (∑ i, G i x • bb i) - φ x = ∑ i, (G i x - ⟪bb i, φ x⟫) • bb i := by
    conv_lhs => rw [hrep]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [sub_smul]
  rw [hdiff]
  calc ‖∑ i, (G i x - ⟪bb i, φ x⟫) • bb i‖ ≤ ∑ i, ‖(G i x - ⟪bb i, φ x⟫) • bb i‖ :=
        norm_sum_le _ _
    _ = ∑ i : Fin d, |G i x - ⟪bb i, φ x⟫| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, bb.norm_eq_one i, Real.norm_eq_abs, mul_one]
    _ ≤ ∑ _i : Fin d, ε' := Finset.sum_le_sum fun i _ => (hG2 i x hx).le
    _ = d * ε' := by simp
    _ < ε := by
        rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [Nat.cast_nonneg (α := ℝ) d]

end Approx

/-! ### Brouwer's fixed point theorem -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Shooting the ray from `x` in the direction `u` hits the unit sphere: the resulting point has
norm one. -/
