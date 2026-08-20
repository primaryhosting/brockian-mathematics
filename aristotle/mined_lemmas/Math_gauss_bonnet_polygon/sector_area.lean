import RequestProject.Wedge

/-!
# Girard's relation for a solid cone over a spherical triangle

Given three vectors `u v w` in `ℝ³` in general position, the region
`Reg u v w`, the part of the unit ball where the three linear forms `⟪u,·⟫`, `⟪v,·⟫`, `⟪w,·⟫`
are nonnegative, has volume `((π - angle v w) + (π - angle u w) + (π - angle u v) - π)/3`.

This is Girard's theorem in disguise: the three quantities `π - angle · ·` are the dihedral
angles of the cone, and three times the volume of the cone is the area of the spherical
triangle it cuts out on the unit sphere.
-/

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-- The closed half-space with inner normal `n`. -/

theorem sector_area (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ < π) (s : ℝ) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < s ∧ 0 ≤ p.1 ∧ 0 ≤ cos θ * p.1 + sin θ * p.2}
      = ENNReal.ofReal ((π - θ) / 2 * s) := by
  have hpi := Real.pi_pos
  rcases le_or_gt s 0 with hs | hs
  · have hemp :
        {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < s ∧ 0 ≤ p.1 ∧ 0 ≤ cos θ * p.1 + sin θ * p.2} = ∅ := by
      ext p
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro h
      nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    rw [hemp, measure_empty, eq_comm, ENNReal.ofReal_eq_zero]
    nlinarith
  · set S : Set (ℝ × ℝ) :=
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < s ∧ 0 ≤ p.1 ∧ 0 ≤ cos θ * p.1 + sin θ * p.2} with hS
    have hSmeas : MeasurableSet S := by
      have : S = ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < s} ∩ {p : ℝ × ℝ | 0 ≤ p.1}) ∩
          {p : ℝ × ℝ | 0 ≤ cos θ * p.1 + sin θ * p.2} := by
        ext p; simp [hS, and_assoc]
      rw [this]
      exact ((measurableSet_lt (by fun_prop) measurable_const).inter
        (measurableSet_le measurable_const (by fun_prop))).inter
        (measurableSet_le measurable_const (by fun_prop))
    rw [← lintegral_indicator_one hSmeas, ← lintegral_comp_polarCoord_symm]
    have hmain : ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • S.indicator (1 : ℝ × ℝ → ENNReal) (polarCoord.symm p)
          = (Ioo (0 : ℝ) (√s) ×ˢ Icc (θ - π / 2) (π / 2)).indicator
              (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p := by
      rintro ⟨r, φ⟩ hp
      obtain ⟨hr, hφ⟩ : r ∈ Ioi (0 : ℝ) ∧ φ ∈ Ioo (-π) π := hp
      have hr0 : 0 < r := hr
      have hiff : (polarCoord.symm (r, φ)) ∈ S ↔
          ((r, φ) ∈ Ioo (0 : ℝ) (√s) ×ˢ Icc (θ - π / 2) (π / 2)) := by
        rw [hS]
        simp only [polarCoord_symm_apply, mem_setOf_eq, mem_prod, mem_Ioo, mem_Icc]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨hr0, ?_⟩,
            (cos_nonneg_pair_iff θ φ hθ0 hθπ hφ).1 ⟨nonneg_of_mul_nonneg_right h2 hr0, ?_⟩⟩
          · have : r ^ 2 < s := by nlinarith [Real.sin_sq_add_cos_sq φ]
            nlinarith [Real.sq_sqrt hs.le, Real.sqrt_pos.2 hs, Real.sqrt_nonneg s]
          · nlinarith
        · rintro ⟨⟨-, h1⟩, h2⟩
          have hc := (cos_nonneg_pair_iff θ φ hθ0 hθπ hφ).2 h2
          refine ⟨?_, by nlinarith [hc.1], by nlinarith [hc.2]⟩
          have : r ^ 2 < s := by nlinarith [Real.sq_sqrt hs.le, Real.sqrt_nonneg s]
          nlinarith [Real.sin_sq_add_cos_sq φ]
      by_cases h : (polarCoord.symm (r, φ)) ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.1 h)]
        simp
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun hc => h (hiff.2 hc)]
        simp
    rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hmain]
    have hA : MeasurableSet (Ioo (0 : ℝ) (√s) ×ˢ Icc (θ - π / 2) (π / 2)) :=
      measurableSet_Ioo.prod measurableSet_Icc
    have hsub : (Ioo (0 : ℝ) (√s) ×ˢ Icc (θ - π / 2) (π / 2)) ⊆ polarCoord.target := by
      rintro ⟨r, φ⟩ ⟨h1, h2⟩
      exact ⟨h1.1, by simp only [mem_Icc] at h2; constructor <;> [linarith [h2.1]; linarith [h2.2]]⟩
    rw [lintegral_indicator hA, Measure.restrict_restrict hA, inter_eq_self_of_subset_left hsub,
      Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Icc]
    rw [lintegral_mul_const' _ _ (by simp), lintegral_ofReal_id_Ioo _ (Real.sqrt_nonneg s),
      Real.sq_sqrt hs.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring_nf

end Math

/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Girard

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The angle sum of a geodesic triangle on the unit sphere exceeds `π` by its area.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-! ### The cross product on `ℝ³` -/

/-- The cross product of two vectors of `ℝ³`. -/
