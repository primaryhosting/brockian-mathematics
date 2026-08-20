import Mathlib
namespace Brockian.MsCeva

/-- Auxiliary: for three non-collinear points `A B C` of the plane, the vectors `B - A` and
`C - A` are linearly independent (stated in the concrete "no nontrivial relation" form). -/

theorem ceva (A B C : EuclideanSpace ℝ (Fin 2)) (u v w : ℝ)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1) (hw : 0 < w ∧ w < 1)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (D E F : EuclideanSpace ℝ (Fin 2))
    (hD : D = B + u • (C - B)) (hE : E = C + v • (A - C)) (hF : F = A + w • (B - A)) :
    (∃ P : EuclideanSpace ℝ (Fin 2),
       (∃ s : ℝ, P = A + s • (D - A)) ∧ (∃ t : ℝ, P = B + t • (E - B)) ∧
       (∃ r : ℝ, P = C + r • (F - C)))
    ↔ (u / (1 - u)) * (v / (1 - v)) * (w / (1 - w)) = 1 := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  obtain ⟨hw0, hw1⟩ := hw
  have hu1' : (1 : ℝ) - u ≠ 0 := by linarith
  have hv1' : (1 : ℝ) - v ≠ 0 := by linarith
  have hw1' : (1 : ℝ) - w ≠ 0 := by linarith
  have hK : u + (1 - u) * (1 - v) ≠ 0 := by nlinarith
  have key : (∃ P : EuclideanSpace ℝ (Fin 2),
       (∃ s : ℝ, P = A + s • (D - A)) ∧ (∃ t : ℝ, P = B + t • (E - B)) ∧
       (∃ r : ℝ, P = C + r • (F - C)))
      ↔ u * v * w = (1 - u) * (1 - v) * (1 - w) := by
    constructor
    · rintro ⟨P, ⟨s, hs⟩, ⟨t, ht⟩, ⟨r, hr⟩⟩
      have h1 : (s * (1 - u) - (1 - t)) • (B - A) + (s * u - t * (1 - v)) • (C - A) = 0 := by
        subst hD hE hF
        linear_combination (norm := module) ht - hs
      have h2 : (s * (1 - u) - r * w) • (B - A) + (s * u - (1 - r)) • (C - A) = 0 := by
        subst hD hE hF
        linear_combination (norm := module) hr - hs
      obtain ⟨p1, p2⟩ := indep_of_not_collinear hABC _ _ h1
      obtain ⟨p3, p4⟩ := indep_of_not_collinear hABC _ _ h2
      exact ceva_alg_forward (s := s) (t := t) (r := r) (by linarith) (by linarith)
        (by linarith) (by linarith)
    · intro hprod
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s * (u + (1 - u) * (1 - v)) = 1 - v :=
        ⟨(1 - v) / (u + (1 - u) * (1 - v)), div_mul_cancel₀ _ hK⟩
      have hs2 : s * (1 - u) + s * u * w = w := by
        refine mul_left_cancel₀ hK ?_
        linear_combination ((1 - u) + u * w) * hs - hprod
      subst hD hE hF
      exact ⟨A + s • ((B + u • (C - B)) - A), ⟨s, rfl⟩,
        ⟨1 - s * (1 - u), ceva_pt_BE A B C u v s hs⟩,
        ⟨1 - s * u, ceva_pt_CF A B C u w s hs2⟩⟩
  rw [key]
  rw [div_mul_div_comm, div_mul_div_comm,
    div_eq_one_iff_eq (by simp [hu1', hv1', hw1'])]

end Brockian.MsCeva

