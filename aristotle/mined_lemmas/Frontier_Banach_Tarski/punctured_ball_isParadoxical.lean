import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
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

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


theorem punctured_ball_isParadoxical :
    IsParadoxical SO3 (Metric.closedBall (0 : E) 1 \ {0}) := by
  obtain ⟨A₁, A₂, hA₁, hA₂, hdisj, he₁, he₂⟩ := sph_isParadoxical
  rw [← cone_sph_eq]
  exact ⟨cone A₁, cone A₂, cone_mono hA₁, cone_mono hA₂, cone_disjoint hdisj,
    cone_equidecomp (hA₁.trans (subset_refl _)) (subset_refl _) he₁,
    cone_equidecomp (hA₂.trans (subset_refl _)) (subset_refl _) he₂⟩

/-! ## Absorbing the centre of the ball -/

/-- Translation by a vector, as a permutation of `ℝ³`. -/
