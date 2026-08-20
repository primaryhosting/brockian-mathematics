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

lemma gauss_bonnet_aux (A B C : E3) (hind : LinearIndependent ℝ ![A, B, C])
    (na nb nc : E3) (hna : na ≠ 0) (hnb : nb ≠ 0) (hnc : nc ≠ 0)
    (hnaa : na = nrm A B C) (hnbb : nb = nrm B C A) (hncc : nc = nrm C A B)
    (e1 : angle na nb = π - sphAngle C A B)
    (e2 : angle nb nc = π - sphAngle A B C)
    (e3 : angle nc na = π - sphAngle B C A) :
    sphAngle A B C + sphAngle B C A + sphAngle C A B = π + sphArea (sphTriangle A B C) := by
  set α := sphAngle A B C
  set β := sphAngle B C A
  set γ := sphAngle C A B
  obtain ⟨hα0, hαp⟩ : 0 ≤ α ∧ α ≤ π := ⟨angle_nonneg _ _, angle_le_pi _ _⟩
  obtain ⟨hβ0, hβp⟩ : 0 ≤ β ∧ β ≤ π := ⟨angle_nonneg _ _, angle_le_pi _ _⟩
  obtain ⟨hγ0, hγp⟩ : 0 ≤ γ ∧ γ ≤ π := ⟨angle_nonneg _ _, angle_le_pi _ _⟩
  have hoct : octantSet na nb nc = solid (sphTriangle A B C) := by
    rw [hnaa, hnbb, hncc, solid_sphTriangle A B C hind]
  have g := girard_volume na nb nc hna hnb hnc
  rw [hoct] at g
  simp only [wedgeSet] at g
  rw [volume_wedge na nb hna hnb, volume_wedge nb nc hnb hnc, volume_wedge nc na hnc hna,
    volume_wedge (-na) (-nb) (neg_ne_zero.2 hna) (neg_ne_zero.2 hnb),
    volume_wedge (-nb) (-nc) (neg_ne_zero.2 hnb) (neg_ne_zero.2 hnc),
    volume_wedge (-nc) (-na) (neg_ne_zero.2 hnc) (neg_ne_zero.2 hna),
    angle_neg_neg, angle_neg_neg, angle_neg_neg, e1, e2, e3, volume_closedBall_E3] at g
  simp only [sub_sub_cancel] at g
  have hfin : volume (solid (sphTriangle A B C)) ≠ ⊤ := by
    have hsub : solid (sphTriangle A B C) ⊆ closedBall (0 : E3) 1 := by
      intro x hx
      simpa [mem_closedBall, dist_zero_right] using hx.1
    exact ne_top_of_le_ne_top (by rw [volume_closedBall_E3]; exact ENNReal.ofReal_ne_top)
      (MeasureTheory.measure_mono hsub)
  set V := (volume (solid (sphTriangle A B C))).toReal with hV
  have hVe : volume (solid (sphTriangle A B C)) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hfin]
  rw [hVe] at g
  have hVnn : 0 ≤ V := ENNReal.toReal_nonneg
  have hpi := Real.pi_pos
  rw [← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith)] at g
  rw [show (4 : ENNReal) = ENNReal.ofReal 4 by simp,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)] at g
  rw [ENNReal.ofReal_eq_ofReal_iff (by linarith) (by positivity)] at g
  rw [sphArea, ← hV]
  linarith

/-- **Gauss–Bonnet / Girard's theorem for a spherical triangle.**
The sum of the interior angles of a geodesic triangle on the unit sphere exceeds `π`
by the area of the triangle. -/
