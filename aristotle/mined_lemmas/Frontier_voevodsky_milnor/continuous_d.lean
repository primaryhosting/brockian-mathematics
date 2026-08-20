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

theorem continuous_d {n : ℕ} {f : Cochain G n} (hf : Continuous f) : Continuous (d G n f) := by
  have h : (d G n f) = (fun g : Fin (n + 1) → G => f (fun i => g i.succ) +
      ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g)) := funext fun g => d_apply n f g
  rw [h]
  refine Continuous.add (hf.comp (continuous_pi fun i => continuous_apply _)) ?_
  exact continuous_finset_sum _ fun j _ => hf.comp (continuous_contractNth G n j)

/-- A homomorphism to the discrete group `ZMod 2` with open kernel is continuous. -/
