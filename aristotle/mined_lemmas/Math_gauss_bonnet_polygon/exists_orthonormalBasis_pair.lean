import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma exists_orthonormalBasis_pair (e0 e1 : E3) (h0 : ‖e0‖ = 1) (h1 : ‖e1‖ = 1)
    (h01 : ⟪e1, e0⟫ = 0) : ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = e0 ∧ b 1 = e1 := by
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp [E3]
  have horth : Orthonormal ℝ (({0, 1} : Set (Fin 3)).restrict ![e0, e1, 0]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    have h10 : ⟪e0, e1⟫ = 0 := by rw [real_inner_comm]; exact h01
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.restrict, h0, h1, h01, h10]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, by simpa using hb 0 (by simp), by simpa using hb 1 (by simp)⟩

/-- The volume of the wedge of the unit ball cut out by two half-spaces with unit normals
`m` and `n`. -/
