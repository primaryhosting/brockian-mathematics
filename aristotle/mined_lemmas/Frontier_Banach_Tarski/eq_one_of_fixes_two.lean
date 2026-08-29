import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Rotations of three dimensional Euclidean space

Explicit rotations about the `z`- and `x`-axes, the cross product, and the fact that a
nontrivial rotation fixes at most two points of the unit sphere.
-/

open scoped RealInnerProductSpace

namespace BT

/-- Three dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A vector of `E3` given by its three coordinates. -/

theorem eq_one_of_fixes_two {g : E3 ≃ₗᵢ[ℝ] E3} (hg : g ∈ CrossPreserving) {u v : E3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) (huv' : u ≠ -v)
    (hgu : g u = u) (hgv : g v = v) : g = 1 := by
  set t : ℝ := ⟪u, v⟫ with ht
  -- `|t| < 1`
  have hCS : |t| ≤ 1 := by
    have := abs_real_inner_le_norm u v
    rwa [hu, hv, one_mul] at this
  have hsub : ‖u - v‖ ^ 2 = 2 - 2 * t := by
    rw [norm_sub_sq_real, hu, hv, ← ht]; ring
  have hadd : ‖u + v‖ ^ 2 = 2 + 2 * t := by
    rw [norm_add_sq_real, hu, hv, ← ht]; ring
  have ht1 : t ≠ 1 := by
    intro h
    apply huv
    have h0 : ‖u - v‖ ^ 2 = 0 := by rw [hsub, h]; ring
    have h1 : u - v = 0 := norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
    exact sub_eq_zero.mp h1
  have ht2 : t ≠ -1 := by
    intro h
    apply huv'
    have h0 : ‖u + v‖ ^ 2 = 0 := by rw [hadd, h]; ring
    have h1 : u + v = 0 := norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
    exact eq_neg_of_add_eq_zero_left h1
  have htsq : t ^ 2 < 1 := by
    rcases lt_or_eq_of_le hCS with h | h
    · nlinarith [abs_nonneg t, sq_abs t]
    · exact absurd (abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp h) (by
        rintro (rfl | rfl) <;> simp_all)
  -- the third vector
  set w : E3 := cross3 u v with hw
  have hwnorm : ‖w‖ ^ 2 = 1 - t ^ 2 := by rw [hw, norm_cross3_sq, hu, hv, ← ht]; ring
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hwnorm
    simp at hwnorm
    nlinarith
  have hgw : g w = w := by rw [hw, hg u v, hgu, hgv]
  -- the second, orthogonalized vector
  set v' : E3 := v - t • u with hv'
  have hgv' : g v' = v' := by rw [hv', map_sub, map_smul, hgu, hgv]
  have hinner_uv' : ⟪u, v'⟫ = 0 := by
    rw [hv', inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, ← ht]
    ring
  have hv'ne : v' ≠ 0 := by
    intro h
    have : v = t • u := by
      have := sub_eq_zero.mp (by rw [← hv']; exact h)
      exact this
    rw [this, norm_smul, hu] at hv
    simp at hv
    nlinarith [sq_abs t]
  have hinner_uw : ⟪u, w⟫ = 0 := inner_cross3_left u v
  have hinner_v'w : ⟪v', w⟫ = 0 := by
    rw [hv', inner_sub_left, real_inner_smul_left, hw, inner_cross3_right, inner_cross3_left]
    ring
  -- linear independence
  have hli : LinearIndependent ℝ ![u, v', w] := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
    · intro i
      fin_cases i
      · intro h; rw [h] at hu; simp at hu
      · exact hv'ne
      · exact hwne
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;>
        first
          | exact hinner_uv'
          | exact hinner_uw
          | exact hinner_v'w
          | (rw [real_inner_comm]; assumption)
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by
    simp [finrank_euclideanSpace]
  have hspan : Submodule.span ℝ (Set.range ![u, v', w]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  -- conclude
  have hfix : ∀ x : E3, g x = x := by
    have hsub : Submodule.span ℝ (Set.range ![u, v', w]) ≤
        LinearMap.eqLocus (g : E3 →ₗ[ℝ] E3) LinearMap.id := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact hgu
      · exact hgv'
      · exact hgw
    intro x
    have : x ∈ LinearMap.eqLocus (g : E3 →ₗ[ℝ] E3) LinearMap.id := by
      rw [hspan] at hsub; exact hsub trivial
    exact this
  exact LinearIsometryEquiv.ext hfix

/-- The fixed points on the unit sphere of a nontrivial cross-product-preserving isometry form a
countable (indeed, at most two-element) set. -/
