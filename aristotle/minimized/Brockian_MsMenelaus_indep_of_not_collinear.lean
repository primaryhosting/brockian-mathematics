import Mathlib
namespace Brockian.MsMenelaus

/-- If `A`, `B`, `C` are not collinear, then `B - A` and `C - A` are linearly independent,
stated concretely as: any vanishing linear combination has zero coefficients. -/

lemma indep_of_not_collinear {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A B C : V) (h : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    ∀ x y : ℝ, x • (B - A) + y • (C - A) = 0 → x = 0 ∧ y = 0 := by
  intro x y hxy
  constructor
  · by_contra hx
    apply h
    rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
    refine ⟨C - A, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    refine ⟨⟨0, by simp⟩, ⟨x⁻¹ * (-y), ?_⟩, ⟨1, by simp⟩⟩
    have h2 : x • (B - A) = (-y) • (C - A) := by linear_combination (norm := module) hxy
    have h3 := congrArg (fun z => (x⁻¹ : ℝ) • z) h2
    simp only [smul_smul, inv_mul_cancel₀ hx, one_smul] at h3
    rw [vadd_eq_add, ← h3]; abel
  · by_contra hy
    apply h
    rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
    refine ⟨B - A, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    refine ⟨⟨0, by simp⟩, ⟨1, by simp⟩, ⟨y⁻¹ * (-x), ?_⟩⟩
    have h2 : y • (C - A) = (-x) • (B - A) := by linear_combination (norm := module) hxy
    have h3 := congrArg (fun z => (y⁻¹ : ℝ) • z) h2
    simp only [smul_smul, inv_mul_cancel₀ hy, one_smul] at h3
    rw [vadd_eq_add, ← h3]; abel

/-- Collinearity criterion for three points written in coordinates with respect to a
linearly independent pair of vectors `b`, `c`: the corresponding determinant vanishes. -/
