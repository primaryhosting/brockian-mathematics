import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
-/

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

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


lemma sph_equidecomp_sdiff (D : Set E) (hD : D.Countable) (hDsub : D ⊆ sph) :
    IsEquidecomposable SO3 sph (sph \ D) := by
  classical
  set P : Set E := {e3, -e3} with hP
  set D₁ : Set E := D \ P with hD1
  set D₂ : Set E := D ∩ P with hD2
  have hD1c : D₁.Countable := hD.mono Set.diff_subset
  have hD2c : D₂.Countable := hD.mono Set.inter_subset_left
  have hc1 : ∀ x ∈ D₁, ∀ y : E, {t : ℝ | toPerm (rotZ t) x = y}.Countable := by
    intro x hx y
    have hxP : x ∉ P := hx.2
    rw [hP, mem_pair_iff] at hxP
    push_neg at hxP
    exact countable_bad_Z x y (axis_ne_zero_of_ne_pole (hDsub hx.1) hxP.1 hxP.2)
  obtain ⟨t, ht⟩ := exists_good_angle rotZ rotZ_pow D₁ hD1c D₁ hD1c hc1
  have stage1 : IsEquidecomposable SO3 sph (sph \ D₁) := by
    refine isEquidecomposable_sdiff_of_iterates sph D₁ (rotZ t) ?_ ?_
    · intro n x hx
      rw [so3_smul]
      exact sph_invariant _ (hDsub hx.1)
    · intro n hn x hx
      rw [so3_smul]
      exact ht x hx n hn
  have hc2 : ∀ x ∈ D₂, ∀ y : E, {t : ℝ | toPerm (rotX t) x = y}.Countable := by
    intro x hx y
    have hxP : x ∈ P := hx.2
    rw [hP, mem_pair_iff] at hxP
    exact countable_bad_X x y (pole_off_xaxis hxP)
  obtain ⟨s, hs⟩ := exists_good_angle rotX rotX_pow D₂ hD2c (D₁ ∪ D₂) (hD1c.union hD2c) hc2
  have stage2 : IsEquidecomposable SO3 (sph \ D₁) ((sph \ D₁) \ D₂) := by
    refine isEquidecomposable_sdiff_of_iterates (sph \ D₁) D₂ (rotX s) ?_ ?_
    · intro n x hx
      rw [so3_smul]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [pow_zero, toPerm_one]
        exact ⟨hDsub hx.1, fun hmem => hmem.2 hx.2⟩
      · exact ⟨sph_invariant _ (hDsub hx.1), fun hmem => hs x hx n hn (Or.inl hmem)⟩
    · intro n hn x hx
      rw [so3_smul]
      exact fun hmem => hs x hx n hn (Or.inr hmem)
  have hunion : (sph \ D₁) \ D₂ = sph \ D := by
    ext v
    constructor
    · rintro ⟨⟨hv, h1⟩, h2⟩
      refine ⟨hv, fun hvD => ?_⟩
      by_cases hp : v ∈ P
      · exact h2 ⟨hvD, hp⟩
      · exact h1 ⟨hvD, hp⟩
    · rintro ⟨hv, hvD⟩
      exact ⟨⟨hv, fun h => hvD h.1⟩, fun h => hvD h.1⟩
  rw [← hunion]
  exact stage1.trans stage2

/-- **The unit sphere in `ℝ³` is paradoxical**, using rotations only. -/
