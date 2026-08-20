/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Set Module Real
open scoped RealInnerProductSpace ENNReal Pointwise

namespace Math

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`. -/

theorem volume_cone_sphTriangle {a b c u v w : E3}
    (hbasis : ∀ x : E3, ∃ α β γ : ℝ, x = α • a + β • b + γ • c)
    (hua : 0 < ⟪u, a⟫) (hub : ⟪u, b⟫ = 0) (huc : ⟪u, c⟫ = 0)
    (hvb : 0 < ⟪v, b⟫) (hvc : ⟪v, c⟫ = 0) (hva : ⟪v, a⟫ = 0)
    (hwc : 0 < ⟪w, c⟫) (hwa : ⟪w, a⟫ = 0) (hwb : ⟪w, b⟫ = 0) :
    volume (Set.Ioo (0:ℝ) 1 • sphTriangle a b c) =
      volume (hemiCone u ∩ hemiCone v ∩ hemiCone w) := by
  have hu0 : u ≠ 0 := fun h => by rw [h] at hua; simp at hua
  have hv0 : v ≠ 0 := fun h => by rw [h] at hvb; simp at hvb
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwc; simp at hwc
  have hinner : ∀ (p : E3) (α β γ : ℝ),
      ⟪p, α • a + β • b + γ • c⟫ = α * ⟪p, a⟫ + β * ⟪p, b⟫ + γ * ⟪p, c⟫ := by
    intro p α β γ
    simp [inner_add_right, real_inner_smul_right]
  -- the intersection of the three half-balls is contained in the cone over the triangle
  have hKsub : hemiCone u ∩ hemiCone v ∩ hemiCone w ⊆ Set.Ioo (0:ℝ) 1 • sphTriangle a b c := by
    rintro x ⟨⟨⟨hx1, hxu⟩, -, hxv⟩, -, hxw⟩
    have hx0 : x ≠ 0 := by rintro rfl; simp at hxu
    have hnorm : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
    obtain ⟨α, β, γ, hx⟩ := hbasis x
    rw [hx, hinner u α β γ, hub, huc] at hxu
    rw [hx, hinner v α β γ, hva, hvc] at hxv
    rw [hx, hinner w α β γ, hwa, hwb] at hxw
    have hα : 0 ≤ α := by nlinarith
    have hβ : 0 ≤ β := by nlinarith
    have hγ : 0 ≤ γ := by nlinarith
    refine Set.mem_smul.mpr ⟨‖x‖, ⟨hnorm, hx1⟩, ‖x‖⁻¹ • x, ⟨?_, ?_⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']
    · refine ⟨‖x‖⁻¹ * α, ‖x‖⁻¹ * β, ‖x‖⁻¹ * γ, by positivity, by positivity, by positivity, ?_⟩
      rw [hx]
      simp [smul_add, smul_smul]
    · rw [smul_inv_smul₀ hnorm.ne']
  -- conversely the cone over the triangle is contained in it up to a null set
  have hZ : volume ({x : E3 | ⟪u, x⟫ = 0} ∪ {x : E3 | ⟪v, x⟫ = 0} ∪ {x : E3 | ⟪w, x⟫ = 0}) = 0 := by
    refine measure_union_null (measure_union_null (volume_inner_eq_zero hu0)
      (volume_inner_eq_zero hv0)) (volume_inner_eq_zero hw0)
  have hCsub : Set.Ioo (0:ℝ) 1 • sphTriangle a b c ⊆ (hemiCone u ∩ hemiCone v ∩ hemiCone w)
      ∪ ({x : E3 | ⟪u, x⟫ = 0} ∪ {x : E3 | ⟪v, x⟫ = 0} ∪ {x : E3 | ⟪w, x⟫ = 0}) := by
    intro x hx
    obtain ⟨t, ⟨ht0, ht1⟩, y, ⟨hy1, α, β, γ, hα, hβ, hγ, hy⟩, hxy⟩ := Set.mem_smul.mp hx
    have hnx : ‖x‖ < 1 := by
      rw [← hxy, norm_smul, hy1, Real.norm_eq_abs, abs_of_pos ht0, mul_one]
      exact ht1
    have hxe : x = (t * α) • a + (t * β) • b + (t * γ) • c := by
      rw [← hxy, hy]
      simp [smul_add, smul_smul]
    have hIu : ⟪u, x⟫ = (t * α) * ⟪u, a⟫ := by rw [hxe, hinner u, hub, huc]; ring
    have hIv : ⟪v, x⟫ = (t * β) * ⟪v, b⟫ := by rw [hxe, hinner v, hva, hvc]; ring
    have hIw : ⟪w, x⟫ = (t * γ) * ⟪w, c⟫ := by rw [hxe, hinner w, hwa, hwb]; ring
    rcases eq_or_lt_of_le hα with hα' | hα'
    · exact Or.inr (Or.inl (Or.inl (by simp [hIu, ← hα'])))
    rcases eq_or_lt_of_le hβ with hβ' | hβ'
    · exact Or.inr (Or.inl (Or.inr (by simp [hIv, ← hβ'])))
    rcases eq_or_lt_of_le hγ with hγ' | hγ'
    · exact Or.inr (Or.inr (by simp [hIw, ← hγ']))
    exact Or.inl ⟨⟨⟨hnx, by rw [hIu]; positivity⟩, hnx, by rw [hIv]; positivity⟩,
      hnx, by rw [hIw]; positivity⟩
  refine le_antisymm ?_ (measure_mono hKsub)
  calc volume (Set.Ioo (0:ℝ) 1 • sphTriangle a b c)
      ≤ volume ((hemiCone u ∩ hemiCone v ∩ hemiCone w)
        ∪ ({x : E3 | ⟪u, x⟫ = 0} ∪ {x : E3 | ⟪v, x⟫ = 0} ∪ {x : E3 | ⟪w, x⟫ = 0})) :=
        measure_mono hCsub
    _ = volume (hemiCone u ∩ hemiCone v ∩ hemiCone w) := measure_union_null_right hZ

/-! ### The Gauss-Bonnet formula for a spherical triangle (Girard's theorem) -/

/-- **Gauss-Bonnet for a spherical triangle** (Girard's theorem): the sum of the interior angles
of a geodesic triangle on the unit sphere exceeds `π` by the area of the triangle. -/
