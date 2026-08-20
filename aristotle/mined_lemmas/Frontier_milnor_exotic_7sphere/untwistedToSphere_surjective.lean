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


lemma untwistedToSphere_surjective {n : ℕ} :
    Function.Surjective (untwistedToSphere (n := n)) := by
  intro v
  obtain ⟨x, t, hxt⟩ := exists_snocLp (v : EuclideanSpace ℝ (Fin (n + 1)))
  have hv : ‖(v : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := norm_coe_unitSphere v
  have hsum : ‖x‖ ^ 2 + t ^ 2 = 1 := by
    rw [← norm_snocLp_sq, ← hxt, hv]; norm_num
  have hxle : ‖x‖ ≤ 1 := by nlinarith [norm_nonneg x, sq_nonneg t]
  have hsq : Real.sqrt (1 - ‖x‖ ^ 2) = |t| := by
    have : (1 : ℝ) - ‖x‖ ^ 2 = t ^ 2 := by linarith
    rw [this, Real.sqrt_sq_eq_abs]
  set d : Dsk n := ⟨x, mem_closedBall_zero_iff.mpr hxle⟩ with hd
  rcases le_total 0 t with ht | ht
  · refine ⟨Quot.mk _ (Sum.inl d), ?_⟩
    apply Subtype.ext
    show snocLp x (1 * Real.sqrt (1 - ‖x‖ ^ 2)) = _
    rw [one_mul, hsq, abs_of_nonneg ht, ← hxt]
  · refine ⟨Quot.mk _ (Sum.inr d), ?_⟩
    apply Subtype.ext
    show snocLp x (-1 * Real.sqrt (1 - ‖x‖ ^ 2)) = _
    rw [hsq, abs_of_nonpos ht, hxt]
    ring_nf

/-- If the two hemisphere coordinates agree with opposite signs, the point is on the equator. -/
