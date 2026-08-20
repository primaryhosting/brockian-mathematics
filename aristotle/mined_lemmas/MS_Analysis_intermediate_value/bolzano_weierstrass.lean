import Mathlib
namespace MS.Analysis

theorem bolzano_weierstrass (s : ℕ → ℝ) (M : ℝ) (hs : ∀ n, |s n| ≤ M) :
    ∃ (a : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (s ∘ φ) Filter.atTop (nhds a) := by
  have hbdd : Bornology.IsBounded (Set.Icc (-M) M) := Metric.isBounded_Icc _ _
  have hmem : ∀ n, s n ∈ Set.Icc (-M) M := fun n => abs_le.1 (hs n)
  obtain ⟨a, -, φ, hφ, htend⟩ := tendsto_subseq_of_bounded hbdd hmem
  exact ⟨a, φ, hφ, htend⟩
