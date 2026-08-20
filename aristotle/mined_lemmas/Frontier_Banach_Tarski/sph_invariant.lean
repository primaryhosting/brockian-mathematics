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


lemma sph_invariant (M : SO3) {v : E} (hv : v ∈ sph) : toPerm M v ∈ sph := by
  have : (toPerm M v).ofLp = M.1 *ᵥ v.ofLp := rfl
  show (toPerm M v).ofLp ⬝ᵥ (toPerm M v).ofLp = 1
  rw [this, dotProduct_mulVec_self]
  exact hv

/-- **The Hausdorff paradox.** There is a countable subset `D` of the unit sphere such that the
complement of `D` in the sphere admits a paradoxical decomposition using rotations. -/
