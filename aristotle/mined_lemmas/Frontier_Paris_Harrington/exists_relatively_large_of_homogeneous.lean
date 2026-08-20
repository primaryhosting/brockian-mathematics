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

lemma exists_relatively_large_of_homogeneous {k n m : ℕ} (c : Finset ℕ → Fin k) (f : ℕ → ℕ)
    (hf : StrictMono f) (a : Fin k) (hom : Homogeneous n c f a) :
    ∃ Y : Finset ℕ, m ≤ Y.card ∧ RelativelyLarge Y ∧ (∀ y ∈ Y, 1 ≤ y) ∧
      ∀ t ⊆ Y, t.card = n → c t = a := by
  classical
  have hsucc : Function.Injective fun i : ℕ => i + 1 := fun x y h => by simpa using h
  set f' : ℕ → ℕ := fun i => f (i + 1) with hf'def
  have hf' : StrictMono f' := fun i j hij => hf (by omega)
  have hpos : ∀ i, 1 ≤ f' i := by
    intro i
    have he : f' i = f (i + 1) := rfl
    have h1 : f 0 < f 1 := hf (by omega)
    have h2 : f 1 ≤ f (i + 1) := hf.monotone (by omega)
    omega
  set M : ℕ := max m (f' 0) with hM
  refine ⟨(Finset.range M).image f', ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hf'.injective, Finset.card_range]
    exact le_max_left _ _
  · have hMpos : 0 < M := lt_of_lt_of_le (hpos 0) (le_max_right _ _)
    have hmem : f' 0 ∈ (Finset.range M).image f' :=
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr hMpos)
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [Finset.card_image_of_injective _ hf'.injective, Finset.card_range]
    exact le_trans (Finset.min'_le _ _ hmem) (le_max_right _ _)
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hpos i
  · intro t ht htc
    have hrange : ∀ x ∈ t, x ∈ Set.range f' := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (ht hx)
      exact ⟨i, rfl⟩
    obtain ⟨s, hs, rfl⟩ := exists_preimage_finset t hrange
    have h2 := hom (s.image fun i => i + 1) (by
      rw [Finset.card_image_of_injective _ hsucc]; omega)
    rw [Finset.image_image] at h2
    exact h2

/-- **Paris–Harrington: the strengthened finite Ramsey theorem is true.**

For all `n, k, m` there is an `N` such that every colouring of the `n`-element subsets of
`{1, …, N}` with `k` colours has a homogeneous set `Y ⊆ {1, …, N}` with at least `m` elements
which is relatively large, i.e. `min Y ≤ |Y|`. -/
