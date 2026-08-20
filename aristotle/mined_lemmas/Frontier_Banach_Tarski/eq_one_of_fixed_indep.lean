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

theorem eq_one_of_fixed_indep (M : Matrix (Fin 3) (Fin 3) ℝ) (horth : M * Mᵀ = 1)
    (hdet : M.det = 1) {u v : Fin 3 → ℝ} (hu : M *ᵥ u = u) (hv : M *ᵥ v = v)
    (hw0 : crossProduct u v ≠ 0) : M = 1 := by
  set w := crossProduct u v with hwdef
  have hMw : M *ᵥ w = w := by
    have h1 := cross_mulVec M u v
    rw [hu, hv, hdet, one_smul] at h1
    calc M *ᵥ w = M *ᵥ (Mᵀ *ᵥ w) := by rw [h1]
      _ = (M * Mᵀ) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = w := by rw [horth, Matrix.one_mulVec]
  set N : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => ![u, v, w] j i) with hN
  have hdetN : N.det ≠ 0 := by
    have hval : N.det = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
      simp only [hN, Matrix.det_fin_three, hwdef, cross_apply]
      simp [Matrix.of_apply]
      ring
    rw [hval]
    intro hzero
    refine hw0 (funext fun k => ?_)
    fin_cases k <;>
      simp <;> nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
  have hcols : ∀ j : Fin 3, M *ᵥ (![u, v, w] j) = ![u, v, w] j := by
    intro j
    fin_cases j
    · exact hu
    · exact hv
    · exact hMw
  have hMN : M * N = N := by
    ext i j
    have h1 : (M * N) i j = (M *ᵥ (![u, v, w] j)) i := rfl
    rw [h1, hcols j]
    rfl
  have hunit : IsUnit N.det := isUnit_iff_ne_zero.mpr hdetN
  calc M = M * (N * N⁻¹) := by rw [Matrix.mul_nonsing_inv _ hunit, mul_one]
    _ = M * N * N⁻¹ := by rw [mul_assoc]
    _ = N * N⁻¹ := by rw [hMN]
    _ = 1 := Matrix.mul_nonsing_inv _ hunit

/-- Two vectors fixed by a nontrivial rotation are parallel. -/
