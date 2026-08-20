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


lemma toWord_lt_mul {x : Bool × Bool} {w : FG} (h : w.toWord.head? ≠ some (flip x)) :
    (lt x * w).toWord = x :: w.toWord := by
  conv_lhs => rw [lt, ← FreeGroup.mk_toWord (x := w)]
  rw [FreeGroup.mul_mk, FreeGroup.toWord_mk, List.singleton_append, FreeGroup.reduce.cons,
    FreeGroup.reduce_toWord]
  cases hw : w.toWord with
  | nil => simp
  | cons hd tl =>
      rw [hw] at h
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
      have hx : ¬ (x.1 = hd.1 ∧ x.2 = !hd.2) := by
        rintro ⟨h1, h2⟩
        exact h (by cases hd; simp_all [flip])
      simp [hx]

/-- The reduced word of an element determines a factorisation into its first letter and the rest. -/
