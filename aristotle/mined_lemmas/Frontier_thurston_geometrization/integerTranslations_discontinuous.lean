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

theorem integerTranslations_discontinuous (K : Set EuclideanThreeSpace) (hK : IsCompact K) :
    {g : EuclideanThreeSpace ≃ᵢ EuclideanThreeSpace |
      g ∈ integerTranslations ∧ ∃ x ∈ K, g x ∈ K}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : EuclideanThreeSpace)
  have hfin : {v : Fin 3 → ℤ | ∀ i, |v i| ≤ ⌈2 * R⌉}.Finite := by
    refine Set.Finite.subset
      (Set.Finite.pi fun _ : Fin 3 => Set.finite_Icc (-⌈2 * R⌉) ⌈2 * R⌉) ?_
    intro v hv i _
    exact ⟨neg_le_of_abs_le (hv i), le_of_abs_le (hv i)⟩
  refine Set.Finite.subset (hfin.image fun v => transl (intVec v)) ?_
  rintro g ⟨hg, x, hxK, hgxK⟩
  obtain ⟨v, rfl⟩ := hg
  refine ⟨v, ?_, rfl⟩
  intro i
  have h1 : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hxK
  have h2 : ‖x + intVec v‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hgxK
  have h3 : ‖intVec v‖ ≤ 2 * R := by
    have hsub : intVec v = (x + intVec v) - x := by abel
    rw [hsub]
    calc ‖(x + intVec v) - x‖ ≤ ‖x + intVec v‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have h4 : |(v i : ℝ)| ≤ 2 * R := by
    have hle := PiLp.norm_apply_le (intVec v) i
    rw [intVec_apply, Real.norm_eq_abs] at hle
    linarith
  have h5 : ((|v i| : ℤ) : ℝ) ≤ ((⌈2 * R⌉ : ℤ) : ℝ) := by
    push_cast
    exact le_trans h4 (Int.le_ceil _)
  exact_mod_cast h5

/-- The action of `ℤ³` on `E³` by translations is cocompact: the closed ball of radius `2`
contains a point of every orbit. -/
