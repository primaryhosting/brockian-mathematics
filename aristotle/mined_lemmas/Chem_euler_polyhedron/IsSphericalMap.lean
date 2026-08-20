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

theorem IsSphericalMap.euler {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a) :
    numOrbits s + numOrbits (a * s) + D.card = numOrbits a + Fintype.card ι + 2 := by
  induction H with
  | @base d₀ d₁ h =>
      have h1 : numOrbits ((1 : Perm ι) * swap d₀ d₁) + 1 = numOrbits (1 : Perm ι) :=
        numOrbits_mul_swap_of_fixed rfl h
      rw [one_mul, numOrbits_one] at h1
      rw [mul_one, numOrbits_one, Finset.card_pair h]
      omega
  | @pendant D s a H d x y hd hx hy hxy ih =>
      have hsx : s x = x := H.vertex_fix hx
      have hsy : s y = y := H.vertex_fix hy
      have hay : a y = y := H.edge_fix hy
      have hdx : d ≠ x := fun h => hx (h ▸ hd)
      have hdy : d ≠ y := fun h => hy (h ▸ hd)
      have hfy : (a * s) y = y := H.face_fix hy
      have hfx : (a * s) x = x := H.face_fix hx
      have hV : numOrbits (s * swap d x) + 1 = numOrbits s :=
        numOrbits_mul_swap_of_fixed hsx hdx
      have hE : numOrbits (a * swap x y) + 1 = numOrbits a :=
        numOrbits_mul_swap_of_fixed hay hxy
      have hF1 : numOrbits ((a * s) * swap d y) + 1 = numOrbits (a * s) :=
        numOrbits_mul_swap_of_fixed hfy hdy
      have hg1x : ((a * s) * swap d y) x = x := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hdx) hxy, hfx]
      have hF2 : numOrbits (((a * s) * swap d y) * swap y x) + 1 =
          numOrbits ((a * s) * swap d y) :=
        numOrbits_mul_swap_of_fixed hg1x (Ne.symm hxy)
      have hid : (a * swap x y) * (s * swap d x) = ((a * s) * swap d y) * swap y x :=
        face_pendant_eq s a hdx hdy hxy hsx hsy hay
      have hcard : (insert x (insert y D)).card = D.card + 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hx]),
          Finset.card_insert_of_notMem hy]
      rw [hid, hcard]
      omega
  | @chord D s a H d e x y hd he hde hface hx hy hxy ih =>
      have hsx : s x = x := H.vertex_fix hx
      have hsy : s y = y := H.vertex_fix hy
      have hax : a x = x := H.edge_fix hx
      have hay : a y = y := H.edge_fix hy
      have hdx : d ≠ x := fun h => hx (h ▸ hd)
      have hdy : d ≠ y := fun h => hy (h ▸ hd)
      have hex : e ≠ x := fun h => hx (h ▸ he)
      have hey : e ≠ y := fun h => hy (h ▸ he)
      have hfy : (a * s) y = y := H.face_fix hy
      have hfx : (a * s) x = x := H.face_fix hx
      have hV1 : numOrbits (s * swap d x) + 1 = numOrbits s :=
        numOrbits_mul_swap_of_fixed hsx hdx
      have hsdxy : (s * swap d x) y = y := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hdy) (Ne.symm hxy), hsy]
      have hV2 : numOrbits ((s * swap d x) * swap e y) + 1 = numOrbits (s * swap d x) :=
        numOrbits_mul_swap_of_fixed hsdxy hey
      have hE : numOrbits (a * swap x y) + 1 = numOrbits a :=
        numOrbits_mul_swap_of_fixed hay hxy
      have hF1 : numOrbits ((a * s) * swap d y) + 1 = numOrbits (a * s) :=
        numOrbits_mul_swap_of_fixed hfy hdy
      have hg1x : ((a * s) * swap d y) x = x := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hdx) hxy, hfx]
      have hF2 : numOrbits (((a * s) * swap d y) * swap e x) + 1 =
          numOrbits ((a * s) * swap d y) :=
        numOrbits_mul_swap_of_fixed hg1x hex
      -- the new edge splits the face containing both `d` and `e`
      have hnot1 : ¬ (a * s).SameCycle d y := fun hc => hdy (hc.eq_of_right hfy)
      have hm1 : ((a * s) * swap d y).SameCycle d y := sameCycle_mul_swap_self hnot1
      have hg1de : ((a * s) * swap d y).SameCycle d e :=
        sameCycle_mono_of_sameCycle_mul_swap hm1 hface
      have hnot2 : ¬ ((a * s) * swap d y).SameCycle e x := fun hc => hex (hc.eq_of_right hg1x)
      have hm2 : (((a * s) * swap d y) * swap e x).SameCycle e x :=
        sameCycle_mul_swap_self hnot2
      have hgde : (((a * s) * swap d y) * swap e x).SameCycle d e :=
        sameCycle_mono_of_sameCycle_mul_swap hm2 hg1de
      have hgd : (((a * s) * swap d y) * swap e x) d = y := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne hde hdx, swap_apply_left, hsy, hay]
      have hgdy : (((a * s) * swap d y) * swap e x).SameCycle d y := ⟨1, by simpa using hgd⟩
      have hgxy : (((a * s) * swap d y) * swap e x).SameCycle x y :=
        hm2.symm.trans (hgde.symm.trans hgdy)
      have hF3 : numOrbits ((((a * s) * swap d y) * swap e x) * swap x y) =
          numOrbits (((a * s) * swap d y) * swap e x) + 1 :=
        numOrbits_mul_swap_of_sameCycle hxy hgxy
      have hid : (a * swap x y) * (s * swap d x * swap e y) =
          (((a * s) * swap d y) * swap e x) * swap x y :=
        face_chord_eq s a hde hdx hdy hex hey hxy hsx hsy hax hay
      have hcard : (insert x (insert y D)).card = D.card + 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hx]),
          Finset.card_insert_of_notMem hy]
      rw [hid, hcard]
      omega

end Polyhedron

namespace Chem

open Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of vertices of a combinatorial map: the number of orbits of the vertex
permutation. -/
