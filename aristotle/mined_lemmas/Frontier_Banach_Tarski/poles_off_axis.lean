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

lemma poles_off_axis : ∀ d ∈ poles, d 0 ≠ 0 ∨ d 2 ≠ 0 := by
  rintro d ⟨hnorm, w, hw, hfix⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h2⟩ := hcon
  have hsum : d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 = 1 := by
    rw [EuclideanSpace.norm_eq] at hnorm
    have h1 : (∑ i, ‖d i‖ ^ 2) = 1 := Real.sqrt_eq_one.mp hnorm
    rw [Fin.sum_univ_three] at h1
    simpa [Real.norm_eq_abs, sq_abs] using h1
  have hd1 : d 1 ^ 2 = 1 := by rw [h0, h2] at hsum; linarith
  set r := d 1 with hr
  have hrne : r ≠ 0 := by intro h; rw [h] at hd1; norm_num at hd1
  have hde : d = r • e2 := by
    ext i
    fin_cases i <;> simp [h0, h2, hr, e2]
  rw [hde, O3.smul_smul_real] at hfix
  exact Phi_smul_e2_ne w hw (smul_right_injective E hrne hfix)

/-- The free group of rotations acts freely on the sphere minus the poles, hence that set is
paradoxical. -/
