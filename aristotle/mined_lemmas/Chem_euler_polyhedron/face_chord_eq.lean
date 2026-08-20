import Mathlib

/-!
# Counting the orbits of a permutation, and how a transposition changes the count

This file develops the basic combinatorial tool behind Euler's polyhedron formula:
for a permutation `f` of a finite type, multiplying by a transposition `swap x y`
either *merges* two orbits (if `x` and `y` lie in different orbits of `f`) or
*splits* one orbit into two (if `x` and `y` lie in the same orbit of `f`).
-/

open Equiv Equiv.Perm Function

namespace Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of orbits (cycles, including fixed points) of a permutation of a finite type. -/

lemma face_chord_eq (s a : Perm ι) {d e x y : ι} (hde : d ≠ e) (hdx : d ≠ x) (hdy : d ≠ y)
    (hex : e ≠ x) (hey : e ≠ y) (hxy : x ≠ y)
    (hsx : s x = x) (hsy : s y = y) (hax : a x = x) (hay : a y = y) :
    (a * swap x y) * (s * swap d x * swap e y) = ((a * s) * swap d y * swap e x) * swap x y := by
  have hsne : ∀ z : ι, z ≠ x → s z ≠ x := fun z hz h => hz (s.injective (h.trans hsx.symm))
  have hsne' : ∀ z : ι, z ≠ y → s z ≠ y := fun z hz h => hz (s.injective (h.trans hsy.symm))
  ext z
  by_cases hzd : z = d
  · rw [hzd]
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hde hdy, swap_apply_of_ne_of_ne hdx hdy,
      swap_apply_of_ne_of_ne hde hdx, swap_apply_left, hsx, hsy, hay]
  by_cases hze : z = e
  · rw [hze]
    simp only [Perm.mul_apply, swap_apply_left, swap_apply_right,
      swap_apply_of_ne_of_ne (Ne.symm hdy) (Ne.symm hxy),
      swap_apply_of_ne_of_ne hex hey, swap_apply_of_ne_of_ne (Ne.symm hdx) hxy, hsy, hsx, hax]
  by_cases hzx : z = x
  · rw [hzx]
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hex) hxy,
      swap_apply_right, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hey) (Ne.symm hxy),
      swap_apply_of_ne_of_ne (hsne d hdx) (hsne' d hdy)]
  by_cases hzy : z = y
  · rw [hzy]
    simp only [Perm.mul_apply, swap_apply_right,
      swap_apply_of_ne_of_ne (Ne.symm hde) hex, swap_apply_of_ne_of_ne (Ne.symm hde) hey,
      swap_apply_of_ne_of_ne (hsne e hex) (hsne' e hey)]
  · simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hze hzy, swap_apply_of_ne_of_ne hzd hzx,
      swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne hze hzx,
      swap_apply_of_ne_of_ne hzd hzy, swap_apply_of_ne_of_ne (hsne z hzx) (hsne' z hzy)]

/-! ### Basic structural facts about spherical maps -/

omit [Fintype ι] in
/-- The permutations of a map fix every non-dart. -/
