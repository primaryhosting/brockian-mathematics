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

theorem Paris_Harrington : StrengthenedFiniteRamsey := by
  classical
  intro n k m
  by_contra hcon
  push_neg at hcon
  choose F hF using hcon
  obtain ⟨c, hc⟩ := exists_limit_coloring (Filter.hyperfilter ℕ) F
  obtain ⟨f, hf, a, hom⟩ := infinite_ramsey n k c
  obtain ⟨Y, hYm, hYlarge, hYpos, hYhom⟩ :=
    exists_relatively_large_of_homogeneous (m := m) c f hf a hom
  have h1 : {N | ∀ s ∈ Y.powersetCard n, F N s = c s} ∈ (Filter.hyperfilter ℕ : Filter ℕ) :=
    limit_coloring_finite_agreement _ F c hc _
  have h2 : {N | ∀ y ∈ Y, y ≤ N} ∈ (Filter.hyperfilter ℕ : Filter ℕ) := by
    refine Nat.hyperfilter_le_atTop ?_
    filter_upwards [Filter.eventually_ge_atTop (Y.sup id)] with N hN y hy
    exact le_trans (Finset.le_sup (f := id) hy) hN
  obtain ⟨N, hN1, hN2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  refine hF N Y ⟨?_, hYm, hYlarge, a, ?_⟩
  · intro y hy
    exact Finset.mem_Icc.mpr ⟨hYpos y hy, hN2 y hy⟩
  · intro t ht htc
    rw [hN1 t (Finset.mem_powersetCard.mpr ⟨ht, htc⟩)]
    exact hYhom t ht htc

/-- The ordinary finite Ramsey theorem is a consequence: for all `n, k, m` there is `N` such that
every `k`-colouring of the `n`-element subsets of `{1, …, N}` has a homogeneous subset of
`{1, …, N}` with at least `m` elements. -/
