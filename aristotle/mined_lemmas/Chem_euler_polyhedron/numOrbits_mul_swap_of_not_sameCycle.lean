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

lemma numOrbits_mul_swap_of_not_sameCycle {f : Perm ι} {x y : ι}
    (h : ¬ f.SameCycle x y) : numOrbits (f * swap x y) + 1 = numOrbits f := by
  classical
  set g := f * swap x y with hg
  have hgxy : g.SameCycle x y := sameCycle_mul_swap_self h
  have hmono : ∀ {a b : ι}, f.SameCycle a b → g.SameCycle a b := fun hab =>
    sameCycle_mono_of_sameCycle_mul_swap hgxy hab
  have hdesc : ∀ {a b : ι}, g.SameCycle a b →
      (f.SameCycle a b ∨ (f.SameCycle a x ∧ f.SameCycle y b) ∨
        (f.SameCycle a y ∧ f.SameCycle x b)) := fun hab => sameCycle_mul_swap_imp hab
  -- the value attached to a `g`-class, seen as an `f`-class different from that of `y`
  have hval : ∀ a : ι, (if f.SameCycle a y then Quotient.mk (SameCycle.setoid f) x
      else Quotient.mk (SameCycle.setoid f) a) ≠ Quotient.mk (SameCycle.setoid f) y := by
    intro a
    split_ifs with hay
    · exact fun hcon => h ((quotient_eq_iff_sameCycle f x y).mp hcon)
    · exact fun hcon => hay ((quotient_eq_iff_sameCycle f a y).mp hcon)
  have hwd : ∀ a b : ι, g.SameCycle a b →
      (if f.SameCycle a y then Quotient.mk (SameCycle.setoid f) x
        else Quotient.mk (SameCycle.setoid f) a) =
      (if f.SameCycle b y then Quotient.mk (SameCycle.setoid f) x
        else Quotient.mk (SameCycle.setoid f) b) := by
    intro a b hab
    rcases hdesc hab with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hay : f.SameCycle a y
      · rw [if_pos hay, if_pos (h1.symm.trans hay)]
      · rw [if_neg hay, if_neg (fun hby => hay (h1.trans hby))]
        exact Quotient.sound h1
    · have hay : ¬ f.SameCycle a y := fun hay => h (h1.symm.trans hay)
      have hby : f.SameCycle b y := h2.symm
      rw [if_neg hay, if_pos hby]
      exact Quotient.sound h1
    · have hay : f.SameCycle a y := h1
      have hby : ¬ f.SameCycle b y := fun hby => h (h2.trans hby)
      rw [if_pos hay, if_neg hby]
      exact Quotient.sound h2
  -- the equivalence
  let toFun : Quotient (SameCycle.setoid g) →
      {q : Quotient (SameCycle.setoid f) // q ≠ Quotient.mk (SameCycle.setoid f) y} :=
    Quotient.lift (fun a => ⟨_, hval a⟩) (by
      intro a b hab
      exact Subtype.ext (hwd a b hab))
  let F : Quotient (SameCycle.setoid f) → Quotient (SameCycle.setoid g) :=
    Quotient.lift (fun a => Quotient.mk (SameCycle.setoid g) a) (by
      intro a b hab
      exact Quotient.sound (hmono hab))
  have hleft : ∀ q, F (toFun q).1 = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      show F (if f.SameCycle a y then Quotient.mk (SameCycle.setoid f) x
        else Quotient.mk (SameCycle.setoid f) a) = _
      by_cases hay : f.SameCycle a y
      · rw [if_pos hay]
        exact Quotient.sound (hgxy.trans (hmono hay).symm)
      · rw [if_neg hay]
        rfl
  have hright : ∀ q : {q : Quotient (SameCycle.setoid f) //
      q ≠ Quotient.mk (SameCycle.setoid f) y}, toFun (F q.1) = q := by
    rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h a =>
      have hay : ¬ f.SameCycle a y := fun hay => hq (Quotient.sound hay)
      apply Subtype.ext
      show (if f.SameCycle a y then Quotient.mk (SameCycle.setoid f) x
        else Quotient.mk (SameCycle.setoid f) a) = _
      rw [if_neg hay]
  have hcard : Nat.card (Quotient (SameCycle.setoid g)) =
      Nat.card {q : Quotient (SameCycle.setoid f) // q ≠ Quotient.mk (SameCycle.setoid f) y} :=
    Nat.card_congr ⟨toFun, fun q => F q.1, hleft, hright⟩
  rw [numOrbits, numOrbits, hcard, card_subtype_ne_add_one]

/-- **Splitting**: multiplying by a transposition of two points of the same orbit increases
the number of orbits by one. -/
