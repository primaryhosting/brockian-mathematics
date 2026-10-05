import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/

theorem tendsto_scaledProb {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {m : ℕ → ℕ} {v : ℝ}
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => scaledProb μ (m n) n) atTop (𝓝 (brownianProb v)) := by
  set S : Set (Set ℝ) := {s | ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ s = Ioc a b} with hS
  have hpi : IsPiSystem S := by
    rintro s ⟨a, b, ha, hb, rfl⟩ u ⟨c, d, hc, hd, rfl⟩ -
    refine ⟨max a c, min b d, ?_, ?_, by rw [Set.Ioc_inter_Ioc]⟩
    · rcases max_choice a c with h | h <;> rw [h] <;> assumption
    · rcases min_choice b d with h | h <;> rw [h] <;> assumption
  have hmeas : ∀ s ∈ S, MeasurableSet s := by
    rintro s ⟨a, b, -, -, rfl⟩
    exact measurableSet_Ioc
  have hnhds : ∀ (u : Set ℝ), IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u := by
    intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu x hx
    set r : ℝ := if x = 0 then ε / 2 else min (ε / 2) (|x| / 2) with hr
    have hr0 : 0 < r := by
      rw [hr]
      split_ifs with hx0
      · linarith
      · have : (0 : ℝ) < |x| := abs_pos.2 hx0
        positivity
    have hrε : r ≤ ε / 2 := by
      rw [hr]; split_ifs
      · exact le_rfl
      · exact min_le_left _ _
    have hne : x - r ≠ 0 ∧ x + r ≠ 0 := by
      rcases eq_or_ne x 0 with rfl | hx0
      · constructor
        · simp only [zero_sub, ne_eq, neg_eq_zero]; exact hr0.ne'
        · simpa using hr0.ne'
      · have hrx : r ≤ |x| / 2 := by
          rw [hr, if_neg hx0]; exact min_le_right _ _
        have hxa : 0 < |x| := abs_pos.2 hx0
        rcases lt_or_gt_of_ne hx0 with hneg | hpos
        · rw [abs_of_neg hneg] at hrx
          constructor <;> intro hc <;> linarith
        · rw [abs_of_pos hpos] at hrx
          constructor <;> intro hc <;> linarith
    refine ⟨Ioc (x - r) (x + r), ⟨_, _, hne.1, hne.2, rfl⟩, ?_, ?_⟩
    · exact Ioc_mem_nhds (by linarith) (by linarith)
    · intro y hy
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have := hy.1; linarith
      · have := hy.2; linarith
  refine hpi.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hnhds ?_
  rintro s ⟨a, b, ha, hb, rfl⟩
  rw [← NNReal.tendsto_coe]
  have hcoe : ∀ ν : ProbabilityMeasure ℝ, ((ν (Ioc a b) : ℝ≥0) : ℝ)
      = (ν : Measure ℝ).real (Ioc a b) := fun ν =>
    (ProbabilityMeasure.measureReal_eq_coe_coeFn ν (Ioc a b)).symm
  simp only [hcoe, scaledProb_toMeasure, brownianProb_toMeasure]
  rcases le_or_gt a b with hab | hab
  · simp only [measureReal_Ioc_eq _ hab]
    exact (tendsto_scaledLaw_measureReal_Iic hmean hvar h3 hm b (Or.inr hb)).sub
      (tendsto_scaledLaw_measureReal_Iic hmean hvar h3 hm a (Or.inr ha))
  · have hempty : Ioc a b = (∅ : Set ℝ) := Ioc_eq_empty (by simp [not_lt.2 hab.le])
    simp [hempty]

/-- **Convergence in distribution of the rescaled random walk.** -/
