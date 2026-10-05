import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

lemma gPart_pos (β : ℝ) {H : (ι → Spin) → ℝ} (hH : Continuous H) : 0 < gPart β H := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := (ι → Spin))).exists_bound_of_continuousOn
    (hH.norm.continuousOn)
  have hbdd : ∀ θ : ι → Spin, Real.exp (-(|β| * M)) ≤ gWeight β H θ := by
    intro θ
    have h1 : |β * H θ| ≤ |β| * M := by
      rw [abs_mul]
      have := hM θ (Set.mem_univ θ)
      have hβ : (0:ℝ) ≤ |β| := abs_nonneg _
      exact mul_le_mul_of_nonneg_left (by simpa using this) hβ
    have h2 : -(|β| * M) ≤ -β * H θ := by
      have := abs_le.1 h1
      simp only [neg_mul]
      linarith [this.1]
    exact Real.exp_le_exp.2 h2
  have hint : Integrable (gWeight β H) (volume : Measure (ι → Spin)) :=
    torus_integrable (continuous_gWeight β hH)
  have hconst : Integrable (fun _ : ι → Spin => Real.exp (-(|β| * M)))
      (volume : Measure (ι → Spin)) := integrable_const _
  have := integral_mono hconst hint hbdd
  have hlow : (0:ℝ) < ∫ _ : ι → Spin, Real.exp (-(|β| * M)) := by
    rw [integral_const, smul_eq_mul]
    exact mul_pos volume_univ_pos (Real.exp_pos _)
  exact lt_of_lt_of_le hlow this

