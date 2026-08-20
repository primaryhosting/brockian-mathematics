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

theorem mem_cocycles_one {f : Cochain G 1} :
    f ∈ cocycles G 1 ↔ Continuous f ∧ ∀ x y : G, f ![x * y] = f ![x] + f ![y] := by
  rw [mem_cocycles]
  refine and_congr_right fun hf => ?_
  constructor
  · intro h x y
    have := congrFun h ![x, y]
    rw [d_apply] at this
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Pi.zero_apply] at this
    have e0 : (fun i : Fin 1 => (![x, y] : Fin 2 → G) i.succ) = ![y] := by
      ext i; fin_cases i; rfl
    have e1 : Fin.contractNth (0 : Fin 2) (· * ·) ![x, y] = ![x * y] := by
      ext i; fin_cases i; simp [Fin.contractNth]
    have e2 : Fin.contractNth (Fin.succ (0 : Fin 1)) (· * ·) ![x, y] = ![x] := by
      ext i; fin_cases i; simp [Fin.contractNth]
    rw [e0, e1, e2] at this
    revert this
    generalize f ![y] = a
    generalize f ![x * y] = b
    generalize f ![x] = c
    revert a b c
    decide
  · intro h
    ext g
    rw [d_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Pi.zero_apply]
    have e0 : (fun i : Fin 1 => g i.succ) = ![g 1] := by
      ext i; fin_cases i; rfl
    have e1 : Fin.contractNth (0 : Fin 2) (· * ·) g = ![g 0 * g 1] := by
      ext i; fin_cases i; simp [Fin.contractNth]
    have e2 : Fin.contractNth (Fin.succ (0 : Fin 1)) (· * ·) g = ![g 0] := by
      ext i; fin_cases i; simp [Fin.contractNth]
    rw [e0, e1, e2, h (g 0) (g 1)]
    generalize f ![g 1] = a
    generalize f ![g 0] = b
    revert a b
    decide

/-- Degree-one cohomology is the group of continuous homomorphisms into `ZMod 2`. -/
