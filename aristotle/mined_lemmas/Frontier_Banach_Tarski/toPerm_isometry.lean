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


lemma toPerm_isometry (M : SO3) : Isometry (toPerm M) := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : toPerm M x - toPerm M y = WithLp.toLp 2 (M.1 *ᵥ (x.ofLp - y.ofLp)) := by
    rw [Matrix.mulVec_sub]
    rfl
  rw [hsub, norm_eq_sqrt_dotProduct, norm_eq_sqrt_dotProduct]
  congr 1
  exact dotProduct_mulVec_self M _

/-- The rotation group of `ℝ³` inside the isometry group. -/
