import Mathlib

/-!
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-! ## The eight Thurston geometries -/

/-- The eight three-dimensional Thurston model geometries. -/
inductive ThurstonGeometry
  /-- Euclidean space `E³`. -/
  | euclidean
  /-- The round sphere `S³`. -/
  | spherical
  /-- Hyperbolic space `H³`. -/
  | hyperbolic
  /-- The product geometry `S² × ℝ`. -/
  | sphereTimesLine
  /-- The product geometry `H² × ℝ`. -/
  | hyperbolicPlaneTimesLine
  /-- The universal cover of `SL(2,ℝ)`. -/
  | slTwoTilde
  /-- Nil geometry (the Heisenberg group). -/
  | nil
  /-- Sol geometry. -/
  | sol
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston geometries. -/

theorem integerTranslations_cocompact :
    ∃ K : Set EuclideanThreeSpace, IsCompact K ∧
      ∀ x : EuclideanThreeSpace, ∃ g ∈ integerTranslations, g x ∈ K := by
  refine ⟨Metric.closedBall 0 2, isCompact_closedBall _ _, ?_⟩
  intro x
  refine ⟨transl (intVec fun i => -⌊x i⌋), ⟨_, rfl⟩, ?_⟩
  have hcoord : ∀ i, |(x + intVec fun i => -⌊x i⌋) i| ≤ 1 := by
    intro i
    have hfr : (x + intVec fun i => -⌊x i⌋) i = Int.fract (x i) := by
      simp [Int.fract, sub_eq_add_neg]
    rw [hfr, abs_of_nonneg (Int.fract_nonneg _)]
    exact le_of_lt (Int.fract_lt_one _)
  simpa [Metric.mem_closedBall, dist_zero_right] using norm_le_two_of_coords hcoord

/-- The integer translations act freely, properly discontinuously and cocompactly on `E³`:
this is the geometric structure of the flat 3-torus. -/
