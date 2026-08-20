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


lemma shiftRot_pow_smul (n : ℕ) (x : E) :
    (shiftRot ^ n) • x = toPerm (rotZ 1 ^ n) (x - cvec) + cvec := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, one_smul, toPerm_one, sub_add_cancel]
  | succ m ih =>
      rw [pow_succ', SemigroupAction.mul_smul, ih]
      show (shiftRot : Equiv.Perm E) _ = _
      show transPerm cvec (toPerm (rotZ 1) (transPerm (-cvec)
        (toPerm (rotZ 1 ^ m) (x - cvec) + cvec))) = _
      have h1 : transPerm (-cvec) (toPerm (rotZ 1 ^ m) (x - cvec) + cvec)
          = toPerm (rotZ 1 ^ m) (x - cvec) := by
        show (toPerm (rotZ 1 ^ m) (x - cvec) + cvec) + -cvec = _
        rw [add_neg_cancel_right]
      rw [h1, ← toPerm_mul, ← pow_succ']
      rfl

