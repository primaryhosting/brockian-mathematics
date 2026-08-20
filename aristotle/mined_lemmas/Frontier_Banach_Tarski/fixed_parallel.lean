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

theorem fixed_parallel (M : Matrix (Fin 3) (Fin 3) ℝ) (horth : M * Mᵀ = 1) (hdet : M.det = 1)
    (hne : M ≠ 1) {u v : Fin 3 → ℝ} (hu : M *ᵥ u = u) (hv : M *ᵥ v = v) (hu0 : u ≠ 0) :
    ∃ c : ℝ, v = c • u := by
  by_cases hc : crossProduct u v = 0
  · exact exists_smul_of_cross_eq_zero hu0 hc
  · exact absurd (eq_one_of_fixed_indep M horth hdet hu hv hc) hne

/-- The unit vectors fixed by a nontrivial rotation form a countable set. -/
