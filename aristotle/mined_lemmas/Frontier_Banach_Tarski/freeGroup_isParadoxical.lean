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


theorem freeGroup_isParadoxical : Frontier.IsParadoxical FG (Set.univ : Set FG) := by
  refine ⟨W (false, true) ∪ W (false, false), W (true, true) ∪ W (true, false),
    Set.subset_univ _, Set.subset_univ _, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro w (hw | hw) (hw' | hw') <;>
      · simp only [W, Set.mem_setOf_eq] at hw hw'
        rw [hw] at hw'
        simp at hw'
  · have := isEquidecomposable_union (false, true)
    simpa [flip] using this
  · have := isEquidecomposable_union (true, true)
    simpa [flip] using this

end FreeGroupParadox

/-! ## Transfer of paradoxical decompositions -/

section Transfer

variable {H X : Type*} [Group H] [MulAction H X]

/-- Equidecomposability can be transported along a group homomorphism which is compatible with
the two actions; in particular from a subgroup to the ambient group. -/
