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

theorem kummerAddHom_mem_cocycles (x : SqCl F) :
    kummerAddHom F x ∈ ContCoh.cocycles (GalF F) 1 := by
  obtain ⟨a, rfl⟩ := sqClass_surjective x
  have hfun : (kummerAddHom F (sqClass a) : ContCoh.Cochain (GalF F) 1)
      = fun g => chiU a (g 0) := rfl
  rw [mem_cocycles_one, hfun]
  refine ⟨(chiU_continuous a).comp (continuous_apply 0), fun x y => ?_⟩
  simpa using chiU_map_mul a x y

/-- The Kummer map `k₁(F) = F^×/(F^×)² → Z¹(G_F, ℤ/2)`. -/
