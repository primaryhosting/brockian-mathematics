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

theorem norm_le_two_of_coords {y : EuclideanThreeSpace} (h : ∀ i, |y i| ≤ 1) : ‖y‖ ≤ 2 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖y i‖ ^ 2 ≤ 4 := by
    have hone : ∀ i : Fin 3, ‖y i‖ ^ 2 ≤ 1 := by
      intro i
      have := h i
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (y i)]
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin 3, (1 : ℝ) := Finset.sum_le_sum fun i _ => hone i
      _ ≤ 4 := by norm_num
  calc Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hsum
    _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The action of `ℤ³` on `E³` by translations is free. -/
