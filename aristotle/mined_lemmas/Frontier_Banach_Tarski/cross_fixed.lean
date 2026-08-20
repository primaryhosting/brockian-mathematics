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


lemma cross_fixed (M : SO3) {u v : Fin 3 → ℝ} (hu : M.1 *ᵥ u = u) (hv : M.1 *ᵥ v = v) :
    M.1 *ᵥ cross3 u v = cross3 u v := by
  have hdet : M.1.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp M.2).2
  have key : (M.1)ᵀ *ᵥ (cross3 (M.1 *ᵥ u) (M.1 *ᵥ v)) = (M.1.det) • cross3 u v := by
    funext i
    fin_cases i <;>
      simp [cross3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three,
        Matrix.transpose_apply] <;> ring
  rw [hu, hv, hdet, one_smul] at key
  calc M.1 *ᵥ cross3 u v = M.1 *ᵥ ((M.1)ᵀ *ᵥ cross3 u v) := by rw [key]
    _ = (M.1 * (M.1)ᵀ) *ᵥ cross3 u v := Matrix.mulVec_mulVec _ _ _
    _ = cross3 u v := by rw [self_mul_transpose, Matrix.one_mulVec]

/-- A rotation fixing two unit vectors which are not equal or opposite is the identity. -/
