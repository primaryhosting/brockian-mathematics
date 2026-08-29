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

theorem exists_small_window (γ : Measure ℝ) [IsProbabilityMeasure γ] [NoAtoms γ] (x : ℝ)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, γ.real (Ioc (x - δ) (x + δ)) ≤ ε := by
  have hanti : Antitone (fun k : ℕ => Ioc (x - 1 / ((k : ℝ) + 1)) (x + 1 / ((k : ℝ) + 1))) := by
    intro a b hab
    have hle : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
    exact Ioc_subset_Ioc (by linarith) (by linarith)
  have hinter : (⋂ k : ℕ, Ioc (x - 1 / ((k : ℝ) + 1)) (x + 1 / ((k : ℝ) + 1))) = {x} := by
    ext y
    simp only [mem_iInter, mem_Ioc, mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < x - y by linarith)
        have := (h k).1
        linarith
      · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < y - x by linarith)
        have := (h k).2
        linarith
    · rintro rfl
      intro k
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      constructor <;> linarith
  have h := tendsto_measure_iInter_atTop (μ := γ)
    (s := fun k : ℕ => Ioc (x - 1 / ((k : ℝ) + 1)) (x + 1 / ((k : ℝ) + 1)))
    (fun k => measurableSet_Ioc.nullMeasurableSet) hanti ⟨0, by simp⟩
  rw [hinter] at h
  simp only [measure_singleton] at h
  have hev : ∀ᶠ k : ℕ in atTop, γ (Ioc (x - 1 / ((k : ℝ) + 1)) (x + 1 / ((k : ℝ) + 1)))
      < ENNReal.ofReal ε := by
    have : (0 : ℝ≥0∞) < ENNReal.ofReal ε := by simpa using hε
    exact h.eventually (eventually_lt_nhds this)
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal hε.le hk.le

/-- Continuity of the distribution function of an atomless probability measure, in the form
needed below. -/
