import Mathlib
namespace Brockian.MsCeva

/-- Auxiliary: for three non-collinear points `A B C` of the plane, the vectors `B - A` and
`C - A` are linearly independent (stated in the concrete "no nontrivial relation" form). -/

lemma indep_of_not_collinear {A B C : EuclideanSpace ℝ (Fin 2)}
    (h : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (x y : ℝ) (hxy : x • (B - A) + y • (C - A) = 0) : x = 0 ∧ y = 0 := by
  by_cases hx : x = 0
  · refine ⟨hx, ?_⟩
    by_contra hy
    subst hx
    simp at hxy
    rcases hxy with hxy | hxy
    · exact absurd hxy hy
    · have hCA : C = A := sub_eq_zero.mp hxy
      subst hCA
      exact h (by simpa [Set.insert_comm, Set.pair_comm] using (collinear_pair ℝ C B))
  · exfalso
    apply h
    have hxy' : x * (-y / x) = -y := by field_simp
    have hB : B - A = (-y / x) • (C - A) := by
      refine smul_right_injective _ hx ?_
      show x • (B - A) = x • ((-y / x) • (C - A))
      rw [smul_smul, hxy']
      linear_combination (norm := module) hxy
    refine (collinear_iff_of_mem (Set.mem_insert A _)).2 ⟨C - A, ?_⟩
    rintro p (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨-y / x, by rw [← hB]; simp⟩
    · exact ⟨1, by simp⟩

/-- Auxiliary algebraic step (forward direction of Ceva). -/
