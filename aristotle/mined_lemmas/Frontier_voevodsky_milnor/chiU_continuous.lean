import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

For a field `F` we define
`k_n(F) = K^M_n(F)/2`, the `n`-th mod-2 Milnor K-group, as the quotient of the `n`-fold
tensor power over `𝔽₂` of the square class group `F^×/(F^×)²` by the Steinberg relations
`{a, 1-a} = 0`.
-/

open scoped TensorProduct

namespace MilnorK

variable (F : Type) [Field F]

/-- The subgroup of squares of `Fˣ`. -/

theorem chiU_continuous (a : Fˣ) : Continuous (chiU a : GalF F → ZMod 2) := by
  have hra : sqrtOf F (a : F) * sqrtOf F (a : F) = algebraMap F (Ksep F) (a : F) :=
    sqrtOf_mul_self F _
  refine ContCoh.continuous_of_isOpen_zero_set _ (fun x y => chiU_map_mul a x y) ?_
  have hset : {σ : GalF F | chiU a σ = 0}
      = (MulAction.stabilizer (GalF F) (sqrtOf F (a : F)) : Set (GalF F)) := by
    ext σ
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    rw [chiU, chi_eq_zero_iff_of_root hra]
    rfl
  rw [hset]
  exact stabilizer_isOpen_of_isIntegral _

