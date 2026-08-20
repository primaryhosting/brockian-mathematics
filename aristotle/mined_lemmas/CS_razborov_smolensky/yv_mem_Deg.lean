import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma yv_mem_Deg (ζ : F) (i : Fin n) : yv F ζ i ∈ Deg F n 1 := by
  have : yv F ζ i = (fun _ : Cube n => (1 : F)) + (ζ - 1) • coord F i := by
    funext x; simp [yv, Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.add_mem _ (const_mem_Deg 1 1) (Submodule.smul_mem _ _ (coord_mem_Deg i le_rfl))

