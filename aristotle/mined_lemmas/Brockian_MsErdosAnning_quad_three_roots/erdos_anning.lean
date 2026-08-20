import Mathlib

/-!
# The Erdős–Anning theorem

An infinite set of points in the Euclidean plane whose pairwise distances are all integers
must be collinear.

## Proof outline

Assume `S` is infinite with integral pairwise distances and pick `A ≠ B` in `S`.  If some
`C ∈ S` is off the line `AB`, then `A`, `B`, `C` form a non-degenerate triangle.  For every
`P ∈ S` the two differences `dist P A - dist P B` and `dist P A - dist P C` are integers
bounded in absolute value by `dist A B` and `dist A C` respectively, so only finitely many
pairs of values occur (`finite_of_not_collinear`).  The heart of the argument (`key`) shows
that three *distinct* points cannot share the same pair of differences: writing
`⟪P - A, B - A⟫` in terms of the distances (`inner_formula`) shows that all such points lie
on a common line `A + p + x • q` with `x = dist P A`, and `‖p + x • q‖ = x` can hold for at
most two values of `x` unless `p = 0` and `‖q‖ = 1` (`key_p_zero`), in which case `B - A`
and `C - A` are both multiples of `q`, contradicting non-collinearity.  Hence `S` would be
finite, a contradiction.
-/

namespace Brockian.MsErdosAnning

open scoped RealInnerProductSpace

/-! ### Auxiliary algebraic lemmas -/

/-- A real quadratic with three distinct roots is identically zero. -/

theorem erdos_anning (S : Set (EuclideanSpace ℝ (Fin 2))) (hinf : S.Infinite)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, dist x y = n) :
    ∃ (p v : EuclideanSpace ℝ (Fin 2)), ∀ x ∈ S, ∃ t : ℝ, x = p + t • v := by
  have h_coll : Collinear ℝ S := Classical.not_not.1 fun h_not_coll => by
    -- S is not collinear, so there exist 3 non-collinear points
    -- Since S is infinite, we can find two distinct points A, B in S
    obtain ⟨A, hA⟩ := hinf.to_subtype.nonempty
    have h_S_nontrivial : ∃ B ∈ S, B ≠ A := by
      by_contra h_all_eq_A
      push_neg at h_all_eq_A
      have : S ⊆ {A} := fun x hx => Set.eq_of_mem_singleton (h_all_eq_A x hx)
      exact hinf (Set.Finite.subset (Set.finite_singleton A) this)
    obtain ⟨B, hB, hBA⟩ := h_S_nontrivial
    -- If S is not collinear, there exists a point C not on the line through A and B
    -- The line through A and B is {A + t • (B - A) | t : ℝ}
    have hC : ∃ C ∈ S, ¬∃ t : ℝ, C = A + t • (B - A) := by
      by_contra h_all_on_line
      push_neg at h_all_on_line
      -- If all points are on the line through A and B, then S is collinear
      apply h_not_coll
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      use A, B - A
      intro x hx
      obtain ⟨t, ht⟩ := h_all_on_line x hx
      use t
      simp [ht]
      rw [add_comm]
    obtain ⟨C, hC_mem, hC_not_line⟩ := hC
    -- A, B, C are not collinear because C is not on the line through A and B
    have hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hcol
      exact hC_not_line (mem_line_of_collinear (Ne.symm hBA) hcol)
    exact hinf (finite_of_not_collinear hint hA hB hC_mem hABC)
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h_coll
  obtain ⟨p₀, v, hv⟩ := h_coll
  use p₀, v
  intro x hx
  obtain ⟨t, ht⟩ := hv x hx
  use t
  simp [ht]
  rw [add_comm]

end Brockian.MsErdosAnning

