import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Existence of an Aronszajn tree

An *Aronszajn tree* is a tree of height `ω₁` all of whose levels are countable and which has no
uncountable chain (equivalently, no uncountable branch).

We construct one in the classical way, from a *coherent sequence* of finite-to-one functions
`E α : α → ℕ` (`α < ω₁`), built by transfinite recursion: `E α` is finite-to-one on `α`, and for
`β < α` the functions `E α ↾ β` and `E β` differ at only finitely many places.  The tree consists
of all pairs `(α, f)` with `α < ω₁` and `f : α → ℕ` differing from `E α` at only finitely many
places, ordered by end-extension.
-/

namespace Frontier

open Ordinal Cardinal Set

/-! ### Countability and `ω₁` -/


theorem levels_countable_aux (α : Ordinal.{0}) : {x : Node | x.lvl = α}.Countable := by
  by_cases hα : α < ω₁
  · set g : Node → Set (Ordinal.{0} × ℕ) :=
      fun x => (fun ξ => (ξ, x.fn ξ)) '' {ξ | ξ < x.lvl ∧ x.fn ξ ≠ E x.lvl ξ} with hg
    have key : ∀ x ∈ {x : Node | x.lvl = α}, ∀ y ∈ {x : Node | x.lvl = α}, g x = g y →
        ∀ ξ : Ordinal.{0}, ξ < α → x.fn ξ ≠ E α ξ → y.fn ξ = x.fn ξ := by
      intro x hx y hy hxy ξ hξ hne
      have hmem : (ξ, x.fn ξ) ∈ g x := ⟨ξ, ⟨by rw [hx]; exact hξ, by rw [hx]; exact hne⟩, rfl⟩
      rw [hxy] at hmem
      obtain ⟨η, -, hη⟩ := hmem
      have h1 : η = ξ := congrArg Prod.fst hη
      have h2 : y.fn η = x.fn ξ := congrArg Prod.snd hη
      rwa [h1] at h2
    refine Set.countable_of_injective_of_countable_image (f := g) ?_ ?_
    · intro x hx y hy hxy
      refine Node.ext' (by rw [hx, hy] : x.lvl = y.lvl) (funext fun ξ => ?_)
      by_cases hξ : ξ < α
      · by_cases hdx : x.fn ξ = E α ξ
        · by_cases hdy : y.fn ξ = E α ξ
          · rw [hdx, hdy]
          · exact key y hy x hx hxy.symm ξ hξ hdy
        · exact (key x hx y hy hxy ξ hξ hdx).symm
      · rw [x.fn_eq_zero (by rw [hx]; exact not_lt.mp hξ),
          y.fn_eq_zero (by rw [hy]; exact not_lt.mp hξ)]
    · have hcount : ((Set.Iio α) ×ˢ (Set.univ : Set ℕ)).Countable :=
        Set.Countable.prod (countable_Iio_iff.mpr hα) Set.countable_univ
      refine Set.Countable.mono ?_ (Set.countable_setOf_finite_subset hcount)
      rintro t ⟨x, hx, rfl⟩
      refine ⟨Set.Finite.image _ x.finite_diff, ?_⟩
      rintro p ⟨ξ, hξ, rfl⟩
      exact ⟨show ξ ∈ Set.Iio α from hx ▸ hξ.1, Set.mem_univ _⟩
  · have hempty : {x : Node | x.lvl = α} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hα (h ▸ x.lvl_lt_omega1)
    rw [hempty]
    exact Set.countable_empty

