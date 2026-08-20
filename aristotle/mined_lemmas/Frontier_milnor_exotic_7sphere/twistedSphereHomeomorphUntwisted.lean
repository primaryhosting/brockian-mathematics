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


noncomputable def twistedSphereHomeomorphUntwisted {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    TwistedSphere f ≃ₜ TwistedSphere (sphereId n) where
  toFun := untwist f
  invFun := untwistInv f
  left_inv := by
    intro z
    induction z using Quot.ind with
    | mk p =>
      cases p with
      | inl x => rfl
      | inr y =>
        show TwistedSphere.mk f (Sum.inr (diskMap f (diskMap f.symm y))) = _
        rw [diskMap_diskMap_symm]
        rfl
  right_inv := by
    intro z
    induction z using Quot.ind with
    | mk p =>
      cases p with
      | inl x => rfl
      | inr y =>
        show TwistedSphere.mk (sphereId n) (Sum.inr (diskMap f.symm (diskMap f y))) = _
        rw [diskMap_symm_diskMap]
        rfl
  continuous_toFun := by
    apply continuous_quot_lift
    exact (TwistedSphere.continuous_mk _).comp
      (continuous_id.sumMap (continuous_diskMap f.symm))
  continuous_invFun := by
    apply continuous_quot_lift
    exact (TwistedSphere.continuous_mk _).comp
      (continuous_id.sumMap (continuous_diskMap f))

/-! ## The untwisted double of the disk is the sphere -/

/-- Append a last coordinate to a Euclidean vector. -/
