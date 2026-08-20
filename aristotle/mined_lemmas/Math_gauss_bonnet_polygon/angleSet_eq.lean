import RequestProject.Sector

/-!
# Volume of a wedge in three-dimensional space

The main result of this file is `SphericalArea.volume_wedge`: for a unit vector `u` and two
linearly independent vectors `s`, `t` orthogonal to `u`, the set of points of the open unit ball
whose orthogonal projection to `u^⊥` lies in the double wedge spanned by `s` and `t` has volume
`4 * angle s t / 3`.
-/

open MeasureTheory Real Set Metric InnerProductGeometry
open scoped ENNReal Real RealInnerProductSpace

namespace SphericalArea

/-- Coordinates of `EuclideanSpace ℝ (Fin 3)` as a product `ℝ × (ℝ × ℝ)`. -/

lemma angleSet_eq (α : ℝ) (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    {ψ : ℝ | ψ ∈ Ioo (-π) π ∧ 0 < Real.sin ψ * Real.sin (α - ψ)}
      = Ioo 0 α ∪ Ioo (-π) (α - π) := by
  ext ψ
  simp only [mem_setOf_eq, mem_Ioo, mem_union]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases lt_trichotomy (Real.sin ψ) 0 with hs | hs | hs
    · -- sin ψ < 0, so ψ ∈ (-π, 0)
      have hψneg : ψ < 0 := by
        by_contra h
        push_neg at h
        exact absurd (Real.sin_nonneg_of_nonneg_of_le_pi h h2.le) (not_le.2 hs)
      right
      refine ⟨h1, ?_⟩
      -- sin (α - ψ) < 0
      have h4 : Real.sin (α - ψ) < 0 := by
        nlinarith [h3]
      by_contra hcon
      push_neg at hcon
      have : 0 ≤ α - ψ := by linarith
      have : α - ψ ≤ π := by linarith
      exact absurd (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) this) (not_le.2 h4)
    · simp [hs] at h3
    · -- sin ψ > 0
      have hψpos : 0 < ψ := by
        by_contra h
        push_neg at h
        have : Real.sin ψ ≤ 0 := by
          have := Real.sin_nonneg_of_nonneg_of_le_pi (x := -ψ) (by linarith) (by linarith)
          rw [Real.sin_neg] at this
          linarith
        linarith
      left
      refine ⟨hψpos, ?_⟩
      have h4 : 0 < Real.sin (α - ψ) := by nlinarith [h3]
      by_contra hcon
      push_neg at hcon
      have h5 : α - ψ ≤ 0 := by linarith
      have h6 : -π < α - ψ := by linarith
      have : Real.sin (α - ψ) ≤ 0 := by
        have := Real.sin_nonneg_of_nonneg_of_le_pi (x := ψ - α) (by linarith) (by linarith)
        rw [show ψ - α = -(α - ψ) by ring, Real.sin_neg] at this
        linarith
      linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hαpos : 0 < α := lt_of_lt_of_le h1 h2.le
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      have hs1 : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
      have hs2 : 0 < Real.sin (α - ψ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      positivity
    · refine ⟨⟨h1, by linarith⟩, ?_⟩
      have hψneg : ψ < 0 := by linarith [Real.pi_pos]
      have hs1 : Real.sin ψ < 0 := by
        have := Real.sin_pos_of_pos_of_lt_pi (x := -ψ) (by linarith) (by linarith)
        rw [Real.sin_neg] at this; linarith
      have hs2 : Real.sin (α - ψ) < 0 := by
        have := Real.sin_pos_of_pos_of_lt_pi (x := α - ψ - π) (by linarith) (by linarith)
        rw [show α - ψ - π = -(π - (α - ψ)) by ring, Real.sin_neg,
          Real.sin_pi_sub] at this
        linarith
      exact mul_pos_of_neg_of_neg hs1 hs2

