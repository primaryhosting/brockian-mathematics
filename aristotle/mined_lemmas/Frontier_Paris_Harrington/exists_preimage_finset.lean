/-
# The infinite Ramsey theorem

Mathlib (as of this project's pinned version) contains no form of Ramsey's theorem, so we develop
the infinite version here, for colourings of `n`-element subsets of `ℕ` with `k` colours.

An infinite homogeneous set is presented as the range of a strictly monotone function `f : ℕ → ℕ`.
-/
import Mathlib

set_option autoImplicit false

namespace Frontier

open Finset

/-- `Homogeneous n c f a` says that every `n`-element subset of the range of `f` has colour `a`. -/

lemma exists_preimage_finset {g : ℕ → ℕ} (t : Finset ℕ)
    (ht : ∀ x ∈ t, x ∈ Set.range g) : ∃ s : Finset ℕ, s.card = t.card ∧ s.image g = t := by
  classical
  refine ⟨t.image (Function.invFun g), ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro x hx z hz hxz
    have hx' := Function.invFun_eq (ht x hx)
    have hz' := Function.invFun_eq (ht z hz)
    rw [← hx', ← hz', hxz]
  · rw [Finset.image_image]
    refine (Finset.image_congr ?_).trans Finset.image_id
    intro x hx
    exact Function.invFun_eq (ht x hx)

/-- One step of the standard construction: given the Ramsey property in dimension `n`, and a
strictly monotone `g`, we can thin out the range of `g` past its first element `g 0` so that the
colour of `{g 0} ∪ t` is constant for `n`-element subsets `t` of the thinned range. -/
