/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.SphericalWedge

/-!
# Gauss Bonnet Polygon

Category: Pure Mathematics.  Target: `Math.gauss_bonnet_polygon`.

## Overview

We prove Girard's theorem (the Gauss–Bonnet theorem for a geodesic triangle on the unit
sphere): the sum of the three interior angles of a spherical triangle equals `π` plus the
area of the triangle.

The area of a region `S` of the unit sphere in `ℝ³` is defined as three times the Lebesgue
volume of the cone over `S` with apex the origin (this is the standard normalisation: the
cone over the whole sphere is the unit ball, of volume `4π/3`, giving total area `4π`).

The proof is the classical "lune" argument.  The three great circles through the pairs of
vertices cut the sphere into eight triangles; each of the three lunes containing the
triangle `T` decomposes as `T` together with one of the neighbouring triangles.
-/

open MeasureTheory Metric Real Set InnerProductGeometry Pointwise

noncomputable section

namespace GaussBonnet

/-! ### Step 4: the normals to the sides of a spherical triangle -/

/-- The interior angle at the vertex `u` of the spherical triangle with vertices `u`, `v`, `w`:
the angle between the tangent directions at `u` of the two geodesics from `u` to `v` and
from `u` to `w`. -/

lemma exists_onb (e1 e2 : E3) (h1 : ‖e1‖ = 1) (h2 : ‖e2‖ = 1) (h12 : inner ℝ e1 e2 = (0 : ℝ)) :
    ∃ B : OrthonormalBasis (Fin 3) ℝ E3, B 0 = e1 ∧ B 1 = e2 := by
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have h21 : inner ℝ e2 e1 = (0 : ℝ) := by rw [real_inner_comm]; exact h12
  have hon : Orthonormal ℝ (({0, 1} : Set (Fin 3)).restrict ![e1, e2, 0]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    simp only [Set.restrict_apply]
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp [h1, h2, h12, h21]
  obtain ⟨B, hB⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨B, hB 0 (by simp), hB 1 (by simp)⟩

/-- An orthonormal frame adapted to a pair of vectors spanning a plane. -/
