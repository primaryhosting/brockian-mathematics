import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

theorem Paradoxical.map {H : Type*} [Group H] [MulAction H X] (ψ : G →* H)
    (hψ : ∀ (g : G) (x : X), (ψ g) • x = g • x) {A : Set X} (h : Paradoxical G A) :
    Paradoxical H A := by
  classical
  obtain ⟨f, g, hfs, hgs, hd, hft, hgt⟩ := h
  have conv : ∀ k : Equidecomp X G, ∃ k' : Equidecomp X H,
      k'.toPartialEquiv = k.toPartialEquiv := by
    intro k
    refine ⟨⟨k.toPartialEquiv, k.witness.image ψ, ?_⟩, rfl⟩
    intro a ha
    obtain ⟨c, hc, hca⟩ := k.isDecompOn a ha
    exact ⟨ψ c, Finset.mem_image_of_mem _ hc, by rw [hψ]; exact hca⟩
  obtain ⟨f', hf'⟩ := conv f
  obtain ⟨g', hg'⟩ := conv g
  have hfs' : f'.source = f.source := congrArg PartialEquiv.source hf'
  have hgs' : g'.source = g.source := congrArg PartialEquiv.source hg'
  have hft' : f'.target = f.target := congrArg PartialEquiv.target hf'
  have hgt' : g'.target = g.target := congrArg PartialEquiv.target hg'
  exact ⟨f', g', hfs' ▸ hfs, hgs' ▸ hgs, hfs' ▸ hgs' ▸ hd, hft' ▸ hft, hgt' ▸ hgt⟩

/-- **Absorption lemma.** If some `ρ : G` pushes `D` into `A` along all its powers,
keeping the positive powers off `D`, then `A \ D` is equidecomposable with `A`. -/
