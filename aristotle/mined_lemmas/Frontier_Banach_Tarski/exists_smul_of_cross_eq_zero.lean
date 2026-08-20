import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

lemma exists_smul_of_cross_eq_zero {u v : Fin 3 → ℝ} (hu : u ≠ 0) (h : crossProduct u v = 0) :
    ∃ c : ℝ, v = c • u := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [cross_apply] at h0 h1 h2
  have hex : ∃ i, u i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu (funext hc)
  obtain ⟨i, hi⟩ := hex
  have main : ∀ i : Fin 3, u i ≠ 0 → ∃ c : ℝ, v = c • u := by
    intro i hi
    refine ⟨v i / u i, ?_⟩
    funext j
    have key : u i * v j = v i * u j := by
      match i, j with
      | 0, 0 => ring
      | 0, 1 => linarith
      | 0, 2 => linarith
      | 1, 0 => linarith
      | 1, 1 => ring
      | 1, 2 => linarith
      | 2, 0 => linarith
      | 2, 1 => linarith
      | 2, 2 => ring
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith
  exact main i hi

/-- A rotation which fixes two vectors with nonzero cross product is the identity: the cross
product is fixed as well, giving an invertible fixed frame. -/
