import Mathlib
namespace Brockian.MsMenelaus

/-- If `A`, `B`, `C` are not collinear, then `B - A` and `C - A` are linearly independent,
stated concretely as: any vanishing linear combination has zero coefficients. -/

lemma collinear_triple_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b c : V) (hbc : ∀ x y : ℝ, x • b + y • c = 0 → x = 0 ∧ y = 0)
    (P : V) (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) :
    Collinear ℝ ({P + x₁ • b + y₁ • c, P + x₂ • b + y₂ • c, P + x₃ • b + y₃ • c} : Set V)
      ↔ (x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁) = 0 := by
  constructor
  · intro hcol
    rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r₂, h2⟩ := hv _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨r₃, h3⟩ := hv _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    rw [vadd_eq_add] at h2 h3
    have e2 : (x₂ - x₁) • b + (y₂ - y₁) • c = r₂ • v := by
      linear_combination (norm := module) h2
    have e3 : (x₃ - x₁) • b + (y₃ - y₁) • c = r₃ • v := by
      linear_combination (norm := module) h3
    have key : (r₃ * (x₂ - x₁) - r₂ * (x₃ - x₁)) • b
        + (r₃ * (y₂ - y₁) - r₂ * (y₃ - y₁)) • c = 0 := by
      linear_combination (norm := module) r₃ • e2 - r₂ • e3
    obtain ⟨kx, ky⟩ := hbc _ _ key
    by_cases hr₂ : r₂ = 0
    · subst hr₂
      have e2' : (x₂ - x₁) • b + (y₂ - y₁) • c = 0 := by rw [e2]; simp
      obtain ⟨p, q⟩ := hbc _ _ e2'
      rw [show x₂ - x₁ = 0 from p, show y₂ - y₁ = 0 from q]; ring
    · have hz : r₂ * ((x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)) = 0 := by
        linear_combination (y₂ - y₁) * kx - (x₂ - x₁) * ky
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h hr₂
      · exact h
  · intro hdet
    rw [collinear_iff_of_mem (Set.mem_insert _ _)]
    by_cases hx : x₂ - x₁ = 0 ∧ y₂ - y₁ = 0
    · obtain ⟨hx2, hy2⟩ := hx
      refine ⟨(x₃ - x₁) • b + (y₃ - y₁) • c, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
      refine ⟨⟨0, by rw [vadd_eq_add]; module⟩,
        ⟨0, by rw [vadd_eq_add, show x₂ = x₁ by linarith, show y₂ = y₁ by linarith]; module⟩,
        ⟨1, by rw [vadd_eq_add]; module⟩⟩
    · have ht : ∃ t : ℝ, x₃ = x₁ + t * (x₂ - x₁) ∧ y₃ = y₁ + t * (y₂ - y₁) := by
        by_cases hx2 : x₂ - x₁ = 0
        · have hy2 : y₂ - y₁ ≠ 0 := fun h => hx ⟨hx2, h⟩
          refine ⟨(y₃ - y₁) / (y₂ - y₁), ?_, ?_⟩
          · have hxx : (x₃ - x₁) * (y₂ - y₁) = 0 := by
              linear_combination -hdet + (y₃ - y₁) * hx2
            rcases mul_eq_zero.1 hxx with h | h
            · rw [hx2]; linarith
            · exact absurd h hy2
          · field_simp
            ring
        · refine ⟨(x₃ - x₁) / (x₂ - x₁), ?_, ?_⟩
          · field_simp
            ring
          · field_simp
            linear_combination hdet
      obtain ⟨t, hx3, hy3⟩ := ht
      subst hx3 hy3
      refine ⟨(x₂ - x₁) • b + (y₂ - y₁) • c, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
      refine ⟨⟨0, by rw [vadd_eq_add]; module⟩, ⟨1, by rw [vadd_eq_add]; module⟩,
        ⟨t, by rw [vadd_eq_add]; module⟩⟩

/-- Menelaus's theorem: points D, E, F on lines BC, CA, AB (with parameters u, v, w) are
    collinear iff the product of signed ratios (u/(1−u))·(v/(1−v))·(w/(1−w)) = −1.

    (Statement adjusted: the nondegeneracy hypothesis `hABC`, that `A`, `B`, `C` form a genuine
    triangle, is required; without it, for a degenerate "triangle" all points are always
    collinear while the product of ratios is arbitrary.) -/
