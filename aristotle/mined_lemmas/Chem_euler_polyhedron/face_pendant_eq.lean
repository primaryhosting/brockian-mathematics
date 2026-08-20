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

lemma face_pendant_eq (s a : Perm ι) {d x y : ι} (hdx : d ≠ x) (hdy : d ≠ y) (hxy : x ≠ y)
    (hsx : s x = x) (hsy : s y = y) (hay : a y = y) :
    (a * swap x y) * (s * swap d x) = (a * s) * swap d y * swap y x := by
  have hsne : ∀ z : ι, z ≠ x → s z ≠ x := fun z hz h => hz (s.injective (h.trans hsx.symm))
  have hsne' : ∀ z : ι, z ≠ y → s z ≠ y := fun z hz h => hz (s.injective (h.trans hsy.symm))
  have hsdx : s d ≠ x := hsne d hdx
  have hsdy : s d ≠ y := hsne' d hdy
  ext z
  by_cases hzd : z = d
  · rw [hzd]
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hdy hdx, swap_apply_left, hsx, hsy, hay]
  by_cases hzx : z = x
  · rw [hzx]
    simp only [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hsdx hsdy]
  by_cases hzy : z = y
  · rw [hzy]
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hdy) (Ne.symm hxy),
      swap_apply_left, swap_apply_right, hsy, hsx,
      swap_apply_of_ne_of_ne (Ne.symm hdx) hxy]
  · simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hzd hzx, swap_apply_of_ne_of_ne hzy hzx,
      swap_apply_of_ne_of_ne hzd hzy, swap_apply_of_ne_of_ne (hsne z hzx) (hsne' z hzy)]

omit [Fintype ι] in
/-- Drawing a chord inserts the two new darts into one face and then splits it with the
transposition `swap x y`. -/
