import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem gauss_bonnet_polygon (u v w : E3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hind : LinearIndependent ℝ ![u, v, w]) :
    sphericalArea (sphericalTriangle u v w)
      = sphAngle u v w + sphAngle v u w + sphAngle w u v - π := by
  obtain ⟨f, g, h, hdec, hcf, hcg, hch⟩ := coords u v w hind
  -- the coordinate functionals are nonzero
  have hf0 : f ≠ 0 := by
    intro hcon; have := hcf 1 0 0; rw [hcon] at this; simp at this
  have hg0 : g ≠ 0 := by
    intro hcon; have := hcg 1 1 0; rw [hcon] at this; simp at this
  have hh0 : h ≠ 0 := by
    intro hcon; have := hch 1 1 1; rw [hcon] at this; simp at this
  have hfin : ∀ k l m : E3 →ₗ[ℝ] ℝ, volume (octant k l m) ≠ ⊤ := fun k l m =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (octant_subset_ball k l m))
  -- permuted linear independence
  have hind₂ : LinearIndependent ℝ ![u, w, v] := by
    have := hind.comp ![0, 2, 1] (by decide)
    convert this using 1
    funext i; fin_cases i <;> rfl
  have hind₃ : LinearIndependent ℝ ![v, w, u] := by
    have := hind.comp ![1, 2, 0] (by decide)
    convert this using 1
    funext i; fin_cases i <;> rfl
  -- the three lunes
  have hLfg : lune f g
      = {x : E3 | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • v + c • w} ∩ ball 0 1 := by
    ext x
    simp only [lune, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, hx1⟩, hx2⟩
      exact ⟨⟨f x, g x, h x, hx1, hx2, (hdec x).symm⟩, hb⟩
    · rintro ⟨⟨a, b, c, ha, hb, rfl⟩, hball⟩
      exact ⟨⟨hball, by rw [hcf]; exact ha⟩, by rw [hcg]; exact hb⟩
  have hLfh : lune f h
      = {x : E3 | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • w + c • v} ∩ ball 0 1 := by
    ext x
    simp only [lune, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, hx1⟩, hx2⟩
      refine ⟨⟨f x, h x, g x, hx1, hx2, ?_⟩, hb⟩
      conv_lhs => rw [← hdec x]
      abel
    · rintro ⟨⟨a, b, c, ha, hb, rfl⟩, hball⟩
      have he : a • u + b • w + c • v = a • u + c • v + b • w := by abel
      rw [he]
      exact ⟨⟨by rwa [he] at hball, by rw [hcf]; exact ha⟩, by rw [hch]; exact hb⟩
  have hLgh : lune g h
      = {x : E3 | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • v + b • w + c • u} ∩ ball 0 1 := by
    ext x
    simp only [lune, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, hx1⟩, hx2⟩
      refine ⟨⟨g x, h x, f x, hx1, hx2, ?_⟩, hb⟩
      conv_lhs => rw [← hdec x]
      abel
    · rintro ⟨⟨a, b, c, ha, hb, rfl⟩, hball⟩
      have he : a • v + b • w + c • u = c • u + a • v + b • w := by abel
      rw [he]
      exact ⟨⟨by rwa [he] at hball, by rw [hcg]; exact ha⟩, by rw [hch]; exact hb⟩
  have hvLfg : volume (lune f g) = ENNReal.ofReal (2 * sphAngle w u v / 3) := by
    rw [hLfg]; exact lune_volume u v w hw hind
  have hvLfh : volume (lune f h) = ENNReal.ofReal (2 * sphAngle v u w / 3) := by
    rw [hLfh]; exact lune_volume u w v hv hind₂
  have hvLgh : volume (lune g h) = ENNReal.ofReal (2 * sphAngle u v w / 3) := by
    rw [hLgh]; exact lune_volume v w u hu hind₃
  -- splitting a lune into two octants, in real form
  have hsplitR : ∀ (k l m : E3 →ₗ[ℝ] ℝ) (θ : ℝ), m ≠ 0 → 0 ≤ θ →
      volume (lune k l) = ENNReal.ofReal θ →
      (volume (octant k l m)).toReal + (volume (octant k l (-m))).toReal = θ := by
    intro k l m θ hm hθ hlv
    have hsp := volume_lune_split k l m hm
    rw [hlv] at hsp
    have := congrArg ENNReal.toReal hsp.symm
    rwa [ENNReal.toReal_add (hfin _ _ _) (hfin _ _ _), ENNReal.toReal_ofReal hθ] at this
  have hang₁ : 0 ≤ sphAngle u v w := angle_nonneg _ _
  have hang₂ : 0 ≤ sphAngle v u w := angle_nonneg _ _
  have hang₃ : 0 ≤ sphAngle w u v := angle_nonneg _ _
  have e₁ := hsplitR f g h _ hh0 (by linarith) hvLfg
  have e₂ := hsplitR f h g _ hg0 (by linarith) hvLfh
  have e₃ := hsplitR g h f _ hf0 (by linarith) hvLgh
  -- reorder the octants appearing in `e₂` and `e₃`
  rw [octant_swap₂₃ f h g, octant_swap₂₃ f h (-g)] at e₂
  rw [octant_swap₂₃ g h f, octant_swap₁₂ g f h, octant_swap₂₃ g h (-f),
    octant_swap₁₂ g (-f) h] at e₃
  -- the total volume of the ball is the sum of the eight octants
  have htot : volume (ball (0 : E3) 1)
      = (volume (octant f g h) + volume (octant f g (-h)))
        + (volume (octant f (-g) h) + volume (octant f (-g) (-h)))
        + ((volume (octant (-f) g h) + volume (octant (-f) g (-h)))
          + (volume (octant (-f) (-g) h) + volume (octant (-f) (-g) (-h)))) := by
    have h1 : volume (ball (0 : E3) 1)
        = volume (ball (0 : E3) 1 ∩ {x | 0 ≤ f x}) + volume (ball (0 : E3) 1 ∩ {x | 0 ≤ (-f) x}) :=
      volume_split _ measurableSet_ball f hf0
    have h2 : volume (ball (0 : E3) 1 ∩ {x | 0 ≤ f x})
        = volume (lune f g) + volume (lune f (-g)) :=
      volume_split _ (measurableSet_ball.inter (measurableSet_halfspace f)) g hg0
    have h3 : volume (ball (0 : E3) 1 ∩ {x | 0 ≤ (-f) x})
        = volume (lune (-f) g) + volume (lune (-f) (-g)) :=
      volume_split _ (measurableSet_ball.inter (measurableSet_halfspace (-f))) g hg0
    rw [h1, h2, h3, volume_lune_split f g h hh0, volume_lune_split f (-g) h hh0,
      volume_lune_split (-f) g h hh0, volume_lune_split (-f) (-g) h hh0]
  -- the antipodal symmetry
  have a₁ := congrArg ENNReal.toReal (volume_octant_neg f g h)
  have a₂ := congrArg ENNReal.toReal (volume_octant_neg f g (-h))
  have a₃ := congrArg ENNReal.toReal (volume_octant_neg f (-g) h)
  have a₄ := congrArg ENNReal.toReal (volume_octant_neg (-f) g h)
  simp only [neg_neg] at a₂ a₃ a₄
  -- convert the total volume identity to real numbers
  have htotR : (volume (octant f g h)).toReal + (volume (octant f g (-h))).toReal
      + ((volume (octant f (-g) h)).toReal + (volume (octant f (-g) (-h))).toReal)
      + (((volume (octant (-f) g h)).toReal + (volume (octant (-f) g (-h))).toReal)
        + ((volume (octant (-f) (-g) h)).toReal + (volume (octant (-f) (-g) (-h))).toReal))
      = 4 * π / 3 := by
    rw [volume_ball_E3] at htot
    have hres := congrArg ENNReal.toReal htot.symm
    rw [ENNReal.toReal_ofReal (by positivity)] at hres
    rw [← hres]
    simp only [ENNReal.toReal_add, hfin, ENNReal.add_ne_top, and_self, ne_eq, not_false_eq_true]
  -- identify the area of the triangle with the volume of the octant
  have hT : Ioo (0 : ℝ) 1 • sphericalTriangle u v w = octant f g h \ {0} := by
    ext y
    constructor
    · rintro ⟨t, ht, x, ⟨hx1, a, b, c, ha, hb, hc, rfl⟩, rfl⟩
      have hnorm : ‖t • (a • u + b • v + c • w)‖ = t := by
        rw [norm_smul, hx1, Real.norm_eq_abs, abs_of_pos ht.1, mul_one]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact mem_ball_zero_iff.2 (by rw [hnorm]; exact ht.2)
      · show 0 ≤ f _
        rw [map_smul, hcf, smul_eq_mul]
        exact mul_nonneg ht.1.le ha
      · show 0 ≤ g _
        rw [map_smul, hcg, smul_eq_mul]
        exact mul_nonneg ht.1.le hb
      · show 0 ≤ h _
        rw [map_smul, hch, smul_eq_mul]
        exact mul_nonneg ht.1.le hc
      · simp only [mem_singleton_iff]
        intro hcon
        rw [hcon, norm_zero] at hnorm
        exact (ne_of_gt ht.1) hnorm.symm
    · rintro ⟨⟨⟨⟨hball, hfx⟩, hgx⟩, hhx⟩, hy0⟩
      have hy0' : y ≠ 0 := by simpa using hy0
      have hnp : 0 < ‖y‖ := norm_pos_iff.2 hy0'
      have hfx' : 0 ≤ f y := hfx
      have hgx' : 0 ≤ g y := hgx
      have hhx' : 0 ≤ h y := hhx
      refine ⟨‖y‖, ⟨hnp, mem_ball_zero_iff.1 hball⟩, ‖y‖⁻¹ • y, ⟨?_, ?_⟩, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hnp), inv_mul_cancel₀ hnp.ne']
      · refine ⟨f (‖y‖⁻¹ • y), g (‖y‖⁻¹ • y), h (‖y‖⁻¹ • y), ?_, ?_, ?_, (hdec _).symm⟩
        · rw [map_smul, smul_eq_mul]
          exact mul_nonneg (inv_pos.2 hnp).le hfx'
        · rw [map_smul, smul_eq_mul]
          exact mul_nonneg (inv_pos.2 hnp).le hgx'
        · rw [map_smul, smul_eq_mul]
          exact mul_nonneg (inv_pos.2 hnp).le hhx'
      · show ‖y‖ • ‖y‖⁻¹ • y = y
        rw [smul_smul, mul_inv_cancel₀ hnp.ne', one_smul]
  have harea : sphericalArea (sphericalTriangle u v w) = 3 * (volume (octant f g h)).toReal := by
    rw [sphericalArea, hT, measure_diff_null (measure_singleton 0)]
  rw [harea]
  linarith [e₁, e₂, e₃, htotR, a₁, a₂, a₃, a₄]

end Math

#print axioms Math.gauss_bonnet_polygon

import Mathlib
import RequestProject.GaussBonnet

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

