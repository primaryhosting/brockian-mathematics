import RequestProject.GaussBonnet.WedgeGeneral
import RequestProject.GaussBonnet.Angle
import RequestProject.GaussBonnet.Girard

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

**Girard's theorem** (the Gauss–Bonnet theorem for a geodesic triangle on the unit sphere):
the sum of the three interior angles of a spherical triangle exceeds `π` by its area.
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric

namespace Math

/-- The inward normal to the side `BC` of the spherical triangle `ABC`, normalised so that
`⟪A, nrm A B C⟫ = 1`. -/

lemma volume_sector_scaled (f R : ℝ) (hf0 : 0 ≤ f) (hfpi : f ≤ π) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2}
      = ENNReal.ofReal (R * ((π - f) / 2)) := by
  rcases le_or_gt R 0 with hR | hR
  · have hsub : {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2}
        ⊆ ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      rintro ⟨x, y⟩ ⟨h1, -, -⟩
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
      simp only at h1 ⊢
      nlinarith [sq_nonneg x, sq_nonneg y]
    have h0 : volume (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]; simp
    rw [measure_mono_null hsub h0, eq_comm, ENNReal.ofReal_eq_zero]
    nlinarith
  · set s := Real.sqrt R with hsdef
    have hs : 0 < s := Real.sqrt_pos.2 hR
    have hs2 : s ^ 2 = R := Real.sq_sqrt hR.le
    have hset : {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2}
        = s • {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.1 ∧ 0 ≤ cos f * p.1 + sin f * p.2} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_smul_set]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨(s⁻¹ * p.1, s⁻¹ * p.2), ⟨?_, ?_, ?_⟩, ?_⟩
        · have h : (s⁻¹ * p.1) ^ 2 + (s⁻¹ * p.2) ^ 2 = (p.1 ^ 2 + p.2 ^ 2) / s ^ 2 := by field_simp
          rw [h, hs2, div_le_one hR]
          exact h1
        · positivity
        · have h : cos f * (s⁻¹ * p.1) + sin f * (s⁻¹ * p.2)
              = s⁻¹ * (cos f * p.1 + sin f * p.2) := by ring
          rw [h]; positivity
        · refine Prod.ext ?_ ?_ <;> simp [Prod.smul_mk] <;> field_simp
      · rintro ⟨q, ⟨h1, h2, h3⟩, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · show (s * q.1) ^ 2 + (s * q.2) ^ 2 ≤ R
          nlinarith [sq_nonneg s]
        · show 0 ≤ s * q.1
          positivity
        · show 0 ≤ cos f * (s * q.1) + sin f * (s * q.2)
          have h : cos f * (s * q.1) + sin f * (s * q.2) = s * (cos f * q.1 + sin f * q.2) := by
            ring
          rw [h]; positivity
    rw [hset, Measure.addHaar_smul, volume_sector f hf0 hfpi]
    rw [show Module.finrank ℝ (ℝ × ℝ) = 2 by simp]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2), hs2, ← ENNReal.ofReal_mul hR.le]

/-- The integral of the cross sectional area factor `1 - t ^ 2` over the real line. -/
