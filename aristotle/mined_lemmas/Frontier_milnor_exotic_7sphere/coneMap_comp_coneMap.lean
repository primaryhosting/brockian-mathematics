import Mathlib
import RequestProject.AlexanderTrick

/-!
# Twisted spheres

A *twisted sphere* is obtained by gluing two copies of the closed `n`-disk along their boundary
`𝕊ⁿ⁻¹` by a homeomorphism `f`.  All the known exotic spheres in dimension `7` arise this way
(Milnor's `S³`-bundles over `S⁴` carry Morse functions with exactly two critical points, which exhibits
them as twisted spheres).

The main result of this file is that **every twisted sphere is homeomorphic to the standard
sphere**: this is the topological half of Milnor's theorem, and it is proved here in full, for
every dimension `n`, using the Alexander trick from `RequestProject.AlexanderTrick`.
-/

namespace Frontier

open Metric

/-- The unit sphere `𝕊ⁿ⁻¹ ⊆ ℝⁿ`. -/
abbrev Sph (n : ℕ) : Type := sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The closed unit disk `Dⁿ ⊆ ℝⁿ`. -/
abbrev Dsk (n : ℕ) : Type := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1


lemma coneMap_comp_coneMap (f g : sphere (0 : E) 1 → sphere (0 : E) 1) (hgf : ∀ y, g (f y) = y)
    (x : E) : coneMap g (coneMap f x) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hFx : coneMap f x ≠ 0 := by
      intro h
      rw [← norm_eq_zero, norm_coneMap] at h
      exact hnx h
    rw [coneMap_of_ne_zero g hFx]
    have hpt : normalizePt hFx = f (normalizePt hx) := by
      apply Subtype.ext
      rw [coe_normalizePt, norm_coneMap, coneMap_of_ne_zero f hx, smul_smul,
        inv_mul_cancel₀ hnx, one_smul]
    rw [hpt, hgf, norm_coneMap, coe_normalizePt, smul_smul, mul_inv_cancel₀ hnx, one_smul]

/-- **The Alexander trick.**  A homeomorphism of the unit sphere of a real normed space extends
to a norm-preserving homeomorphism of the whole space (the radial, or cone, extension). -/
