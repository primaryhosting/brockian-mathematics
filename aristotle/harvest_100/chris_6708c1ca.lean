/-
Basic theory of "almost equality" (equality off a finite set) of functions
`Ordinal → ℕ` below a given ordinal, used in the construction of an Aronszajn tree.
-/
import Mathlib

open Cardinal Ordinal Set

namespace Aronszajn

/-- `AlmostEq a f g` means that `f` and `g` agree at all but finitely many `ξ < a`. -/
def AlmostEq (a : Ordinal.{0}) (f g : Ordinal.{0} → ℕ) : Prop :=
  {ξ : Ordinal.{0} | ξ < a ∧ f ξ ≠ g ξ}.Finite

/-- `Nice a f` means that `f` is injective on `Set.Iio a` and its image there omits
infinitely many natural numbers. -/
def Nice (a : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : Prop :=
  Set.InjOn f (Set.Iio a) ∧ (f '' Set.Iio a)ᶜ.Infinite

variable {a b : Ordinal.{0}} {f g h : Ordinal.{0} → ℕ}

theorem almostEq_of_eqOn (hfg : ∀ ξ < a, f ξ = g ξ) : AlmostEq a f g := by
  have : {ξ : Ordinal.{0} | ξ < a ∧ f ξ ≠ g ξ} = ∅ := by
    ext ξ; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩; exact h2 (hfg ξ h1)
  rw [AlmostEq, this]; exact Set.finite_empty

theorem almostEq_refl (a : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : AlmostEq a f f :=
  almostEq_of_eqOn fun _ _ => rfl

theorem AlmostEq.symm (hfg : AlmostEq a f g) : AlmostEq a g f := by
  refine hfg.subset ?_
  rintro ξ ⟨h1, h2⟩
  exact ⟨h1, fun hh => h2 hh.symm⟩

theorem AlmostEq.trans (hfg : AlmostEq a f g) (hgh : AlmostEq a g h) : AlmostEq a f h := by
  refine (hfg.union hgh).subset ?_
  rintro ξ ⟨h1, h2⟩
  by_cases hx : f ξ = g ξ
  · exact Or.inr ⟨h1, by rw [← hx]; exact h2⟩
  · exact Or.inl ⟨h1, hx⟩

theorem AlmostEq.mono (hab : a ≤ b) (hfg : AlmostEq b f g) : AlmostEq a f g := by
  refine hfg.subset ?_
  rintro ξ ⟨h1, h2⟩
  exact ⟨lt_of_lt_of_le h1 hab, h2⟩

theorem AlmostEq.congr_left (hff : ∀ ξ < a, f ξ = h ξ) (hfg : AlmostEq a f g) :
    AlmostEq a h g :=
  (almostEq_of_eqOn hff).symm.trans hfg

/-- If `f` and `g` are almost equal below `a`, the image of `f` is contained in the image of
`g` together with a finite set. -/
theorem AlmostEq.image_subset_union (hfg : AlmostEq a f g) :
    ∃ F : Set ℕ, F.Finite ∧ f '' Set.Iio a ⊆ g '' Set.Iio a ∪ F := by
  refine ⟨f '' {ξ : Ordinal.{0} | ξ < a ∧ f ξ ≠ g ξ}, hfg.image _, ?_⟩
  rintro n ⟨ξ, hξ, rfl⟩
  by_cases hx : f ξ = g ξ
  · exact Or.inl ⟨ξ, hξ, hx.symm⟩
  · exact Or.inr ⟨ξ, ⟨hξ, hx⟩, rfl⟩

theorem AlmostEq.coinfinite (hfg : AlmostEq a f g) (hg : (g '' Set.Iio a)ᶜ.Infinite) :
    (f '' Set.Iio a)ᶜ.Infinite := by
  obtain ⟨F, hF, hsub⟩ := hfg.image_subset_union
  refine Set.Infinite.mono ?_ (hg.diff hF)
  intro n hn
  simp only [Set.mem_diff, Set.mem_compl_iff] at hn
  simp only [Set.mem_compl_iff]
  intro hmem
  rcases hsub hmem with h1 | h1
  · exact hn.1 h1
  · exact hn.2 h1

theorem Nice.injOn (hf : Nice a f) : Set.InjOn f (Set.Iio a) := hf.1

theorem Nice.coinfinite (hf : Nice a f) : (f '' Set.Iio a)ᶜ.Infinite := hf.2

/-- From a nice function one can always find an unused value avoiding a finite set. -/
theorem Nice.exists_fresh (hf : Nice a f) (M : Finset ℕ) :
    ∃ m : ℕ, m ∉ f '' Set.Iio a ∧ m ∉ M := by
  have : ((f '' Set.Iio a)ᶜ \ (M : Set ℕ)).Infinite := hf.2.diff M.finite_toSet
  obtain ⟨m, hm⟩ := this.nonempty
  exact ⟨m, hm.1, hm.2⟩

end Aronszajn

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

