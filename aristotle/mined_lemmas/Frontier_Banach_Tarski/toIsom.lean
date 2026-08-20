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


def toIsom : SO3 →* IsomGroup where
  toFun M := ⟨toPerm M, toPerm_isometry M⟩
  map_one' := Subtype.ext (Equiv.ext fun v => by
    show WithLp.toLp 2 ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.ofLp) = v
    rw [Matrix.one_mulVec])
  map_mul' M N := Subtype.ext (Equiv.ext fun v => by
    show WithLp.toLp 2 ((M.1 * N.1) *ᵥ v.ofLp) = WithLp.toLp 2 (M.1 *ᵥ (N.1 *ᵥ v.ofLp))
    rw [← Matrix.mulVec_mulVec])

