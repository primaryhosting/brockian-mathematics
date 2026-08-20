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

lemma exists_inner_eq {A B C : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) (r1 r2 : ℝ) :
    ∃ q : EuclideanSpace ℝ (Fin 2), ⟪q, B - A⟫ = r1 ∧ ⟪q, C - A⟫ = r2 := by
  -- Define the linear map T(q) = (⟪q, B - A⟫, ⟪q, C - A⟫)
  let T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ × ℝ := {
    toFun := fun q => (⟪q, B - A⟫, ⟪q, C - A⟫)
    map_add' := fun x y => by simp [inner_add_left]
    map_smul' := fun c x => by simp [inner_smul_left]
  }
  -- T has trivial kernel by orth_eq_zero
  have hker : LinearMap.ker T = ⊥ := by
    ext q
    simp only [LinearMap.mem_ker, Submodule.mem_bot, Prod.ext_iff]
    constructor
    · intro hq
      exact orth_eq_zero hABC hq.1 hq.2
    · intro hq
      simp [hq]
  -- T is surjective since dim(domain) = dim(codomain) and ker(T) = ⊥
  have hsurj : Function.Surjective T := by
    have hidj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
    have hcodim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
    have h := LinearMap.finrank_range_of_inj hidj
    have hrange_dim : Module.finrank ℝ (LinearMap.range T) = Module.finrank ℝ (ℝ × ℝ) := by
      rw [h, hfin, hcodim]
    -- The range has same dimension as codomain, so it's the whole space
    have hrange : LinearMap.range T = ⊤ := Submodule.eq_top_of_finrank_eq hrange_dim
    exact LinearMap.range_eq_top.mp hrange
  obtain ⟨q, hq⟩ := hsurj (r1, r2)
  have hq' : (⟪q, B - A⟫, ⟪q, C - A⟫) = (r1, r2) := hq
  exact ⟨q, congrArg Prod.fst hq', congrArg Prod.snd hq'⟩

/-- The basic identity relating the inner product `⟪P - A, B - A⟫` to the distances from `P`. -/
