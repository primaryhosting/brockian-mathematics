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

lemma ramsey_step {k n : ℕ}
    (IH : ∀ d : Finset ℕ → Fin k, ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ a : Fin k, Homogeneous n d f a)
    (c : Finset ℕ → Fin k) (g : ℕ → ℕ) (hg : StrictMono g) :
    ∃ (g' : ℕ → ℕ) (a : Fin k), StrictMono g' ∧ (∀ i, g 0 < g' i) ∧
      (∀ i, ∃ j, g' i = g j) ∧
      ∀ s : Finset ℕ, s.card = n → c (insert (g 0) (s.image g')) = a := by
  classical
  obtain ⟨h, hh, α, hom⟩ := IH fun t => c (insert (g 0) (t.image fun i => g (i + 1)))
  refine ⟨fun i => g (h i + 1), α, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hg (by have := hh hij; omega)
  · intro i
    exact hg (by omega)
  · intro i
    exact ⟨h i + 1, rfl⟩
  · intro s hs
    have h2 := hom s hs
    simp only [Finset.image_image] at h2
    exact h2

/-- **Infinite Ramsey theorem.** For every colouring of the finite subsets of `ℕ` with `k` colours
there is an infinite set (the range of a strictly monotone `f`) all of whose `n`-element subsets
receive the same colour. -/
