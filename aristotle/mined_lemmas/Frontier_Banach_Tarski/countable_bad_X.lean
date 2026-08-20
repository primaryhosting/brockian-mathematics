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


lemma countable_bad_X (x y : E) (hx : (x.ofLp 1) ^ 2 + (x.ofLp 2) ^ 2 ≠ 0) :
    {t : ℝ | toPerm (rotX t) x = y}.Countable := by
  set r : ℝ := (x.ofLp 1) ^ 2 + (x.ofLp 2) ^ 2 with hr
  refine Set.Countable.mono (s₂ := {t : ℝ | Real.cos t =
      (x.ofLp 1 * y.ofLp 1 + x.ofLp 2 * y.ofLp 2) / r ∧
      Real.sin t = (x.ofLp 1 * y.ofLp 2 - x.ofLp 2 * y.ofLp 1) / r}) ?_ (countable_cos_sin _ _)
  intro t ht
  have h0 : Real.cos t * x.ofLp 1 - Real.sin t * x.ofLp 2 = y.ofLp 1 := by
    have h2 : (toPerm (rotX t) x).ofLp 1 = y.ofLp 1 := by rw [show toPerm (rotX t) x = y from ht]
    rw [rotX_apply] at h2
    simpa using h2
  have h1 : Real.sin t * x.ofLp 1 + Real.cos t * x.ofLp 2 = y.ofLp 2 := by
    have h2 : (toPerm (rotX t) x).ofLp 2 = y.ofLp 2 := by rw [show toPerm (rotX t) x = y from ht]
    rw [rotX_apply] at h2
    simpa using h2
  constructor
  · rw [eq_div_iff hx, hr]
    linear_combination x.ofLp 1 * h0 + x.ofLp 2 * h1
  · rw [eq_div_iff hx, hr]
    linear_combination x.ofLp 1 * h1 - x.ofLp 2 * h0

/-- Given a countable set `D` of starting points and a countable target set `C`, all but
countably many angles `t` have the property that no positive iterate of the rotation `rot t`
maps a point of `D` into `C`. -/
