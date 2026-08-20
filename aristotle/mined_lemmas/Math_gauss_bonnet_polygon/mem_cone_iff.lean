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

theorem mem_cone_iff (hd : 0 < d)
    (hua : (inner ℝ u a : ℝ) = d) (hub : (inner ℝ u b : ℝ) = 0) (huc : (inner ℝ u c : ℝ) = 0)
    (hva : (inner ℝ v a : ℝ) = 0) (hvb : (inner ℝ v b : ℝ) = d) (hvc : (inner ℝ v c : ℝ) = 0)
    (hwa : (inner ℝ w a : ℝ) = 0) (hwb : (inner ℝ w b : ℝ) = 0) (hwc : (inner ℝ w c : ℝ) = d)
    (hspan : ∀ x : E3, ∃ p q r : ℝ, x = p • a + q • b + r • c) (x : E3) :
    (∃ p q r : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ 0 ≤ r ∧ x = p • a + q • b + r • c) ↔
      (0 ≤ (inner ℝ u x : ℝ) ∧ 0 ≤ (inner ℝ v x : ℝ) ∧ 0 ≤ (inner ℝ w x : ℝ)) := by
  have key : ∀ (n : E3) (na nb nc : ℝ), (inner ℝ n a : ℝ) = na → (inner ℝ n b : ℝ) = nb →
      (inner ℝ n c : ℝ) = nc → ∀ p q r : ℝ, (inner ℝ n (p • a + q • b + r • c) : ℝ)
        = p * na + q * nb + r * nc := by
    intro n na nb nc h1 h2 h3 p q r
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, h1, h2, h3]
  constructor
  · rintro ⟨p, q, r, hp, hq, hr, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [key u d 0 0 hua hub huc]; nlinarith
    · rw [key v 0 d 0 hva hvb hvc]; nlinarith
    · rw [key w 0 0 d hwa hwb hwc]; nlinarith
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨p, q, r, rfl⟩ := hspan x
    rw [key u d 0 0 hua hub huc] at h1
    rw [key v 0 d 0 hva hvb hvc] at h2
    rw [key w 0 0 d hwa hwb hwc] at h3
    exact ⟨p, q, r, by nlinarith, by nlinarith, by nlinarith, rfl⟩

/-- The cone over the spherical triangle, intersected with the unit ball, is the region
`Reg u v w` cut out by the dual frame. -/
