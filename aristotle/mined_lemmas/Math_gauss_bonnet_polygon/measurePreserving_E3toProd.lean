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

theorem measurePreserving_E3toProd : MeasurePreserving E3toProd volume volume := by
  have h1 : MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have h2 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have h3 : MeasurePreserving (fun q : ℝ × (Fin 2 → ℝ) =>
      ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow) q) volume volume :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  exact (h3.comp h2).comp h1

