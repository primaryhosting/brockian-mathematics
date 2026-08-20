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

theorem d_zero_eq_zero (f : Cochain G 0) : d G 0 f = 0 := by
  ext g
  rw [d_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Pi.zero_apply]
  rw [Subsingleton.elim (fun i => g i.succ) (Fin.contractNth 0 (· * ·) g)]
  generalize f (Fin.contractNth 0 (· * ·) g) = a
  revert a
  decide

variable (G)

/-- Continuous `n`-cochains, as a submodule of all cochains. -/
