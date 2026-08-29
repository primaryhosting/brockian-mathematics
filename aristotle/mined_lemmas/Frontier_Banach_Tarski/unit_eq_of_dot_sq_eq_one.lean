import RequestProject.Equidecomp

/-!
# Rotations of `ℝ³`

Set-up for the Banach–Tarski paradox: the group `SO(3)` of rotations acting on
`E = EuclideanSpace ℝ (Fin 3)`, the group of isometries of `E`, and the fact that a
non-identity rotation fixes at most two points of the unit sphere.
-/

open Matrix

namespace BanachTarski

/-- Three dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The group of rotations of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

noncomputable instance : SMul ↥SO3 E :=
  ⟨fun M x => WithLp.toLp 2 ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x)⟩


theorem unit_eq_of_dot_sq_eq_one {p q : Fin 3 → ℝ} (hp : p ⬝ᵥ p = 1) (hq : q ⬝ᵥ q = 1)
    (h : (p ⬝ᵥ q) ^ 2 = 1) : q = p ∨ q = -p := by
  set c := p ⬝ᵥ q with hc
  have hr : (q - c • p) ⬝ᵥ (q - c • p) = 0 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, hp, hq,
      smul_eq_mul]
    rw [dotProduct_comm q p, ← hc]
    nlinarith [h]
  have hq' : q = c • p := by
    have h0 : q - c • p = 0 := dotProduct_self_eq_zero.mp hr
    have := sub_eq_zero.mp h0
    exact this
  have hcc : (c - 1) * (c + 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hcc with h1 | h1
  · left
    rw [hq', show c = 1 by linarith, one_smul]
  · right
    rw [hq', show c = -1 by linarith]
    ext i
    simp

end BanachTarski

import Mathlib

/-!
# Equidecomposability and paradoxical decompositions

This file develops the elementary theory of equidecomposability of subsets of a `G`-set `X`.

Two sets `A B ⊆ X` are *equidecomposable* if there is a bijection `A → B` which is piecewise
given by finitely many elements of `G`.  This is equivalent to the usual formulation with
finite partitions (see `RequestProject.Pieces`), but is much more convenient to work with.
-/

namespace BanachTarski

open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

/-- `A` and `B` are equidecomposable with respect to the group `G` acting on `X`: there is a
bijection from `A` to `B` which is piecewise given by finitely many elements of `G`. -/
