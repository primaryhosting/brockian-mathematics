/-
Classical `XY`-type models with a continuous (rotation) symmetry, and the
Mermin–Wagner / Pfister "two–shift" bound on the magnetization in terms of the
Dirichlet energy of a cut-off function.
-/
import Mathlib

open MeasureTheory Real

noncomputable section

namespace MerminWagner

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`.  The continuous symmetry group of the
models below is the rotation group of this circle acting diagonally on all spins. -/
abbrev Spin : Type := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

lemma partition_pos (β : ℝ) (hb : ∀ x, Continuous (b x)) : 0 < partition β J b := by
  have hcont : Continuous (gibbsWeight β J b) := continuous_gibbsWeight β hb
  obtain ⟨θ₀, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := V → Spin)) hcont.continuousOn
  have hc : 0 < gibbsWeight β J b θ₀ := gibbsWeight_pos β θ₀
  have hle : ∀ θ, gibbsWeight β J b θ₀ ≤ gibbsWeight β J b θ := fun θ =>
    hmin (Set.mem_univ θ)
  have h1 : ∫ _ : V → Spin, gibbsWeight β J b θ₀ ∂(refMeasure V) ≤ partition β J b := by
    refine integral_mono (integrable_const _) (integrable_of_continuous hcont) ?_
    intro θ; exact hle θ
  have h2 : (0:ℝ) < ∫ _ : V → Spin, gibbsWeight β J b θ₀ ∂(refMeasure V) := by
    rw [integral_const, smul_eq_mul]
    have : 0 < ((refMeasure V) Set.univ).toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨refMeasure_univ_pos, measure_lt_top _ _⟩
    positivity
  linarith

end Continuity

section MainBound

variable {J : V → V → ℝ} {b : V → Spin → ℝ} {f : V → ℝ} {β : ℝ} {x₀ : V} {φ : Spin}

/-- The shift of a configuration by `π f`. -/
