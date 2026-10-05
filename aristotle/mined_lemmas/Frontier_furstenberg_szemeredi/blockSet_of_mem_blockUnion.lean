/-
Companion file to `RequestProject.FurstenbergSzemeredi`.

Here we prove the *converse* reduction: if every subset of `ℕ` of positive upper density
contains arithmetic progressions of length `k`, then the finitary Szemerédi property
`SzemerediFinitaryAt k` holds.  Consequently the hypothesis used in
`Frontier.furstenberg_szemeredi` is exactly equivalent to its conclusion, so the reduction
is lossless.

The proof is by contraposition: from a family of progression-free subsets of `[0, M)` of
density `≥ δ` with `M` arbitrarily large, we build a single set of positive upper density
with no progression of length `k`, by placing the `j`-th example in the interval
`[2 Lⱼ, 3 Lⱼ)` with the lengths `Lⱼ` growing at least geometrically with ratio `300`.
-/

import Mathlib
import RequestProject.FurstenbergSzemeredi

namespace Frontier

open scoped Classical

section Converse

variable (Mf : ℕ → ℕ) (Sf : ℕ → Finset ℕ)

/-- The thresholds used to select the successive blocks. -/

theorem blockSet_of_mem_blockUnion (hM : ∀ N, N ≤ Mf N)
    (hSub : ∀ N, Sf N ⊆ Finset.range (Mf N)) {x j : ℕ} (hx : x ∈ blockUnion Mf Sf)
    (h1 : 2 * blockLen Mf j ≤ x) (h2 : x < 3 * blockLen Mf j) : x ∈ blockSet Mf Sf j := by
  rw [mem_blockUnion_iff] at hx
  obtain ⟨i, hi⟩ := hx
  obtain ⟨hi1, hi2⟩ := blockSet_bounds hSub hi
  rcases lt_trichotomy i j with h | h | h
  · exfalso
    have := blockLen_growth hM h
    omega
  · subst h; exact hi
  · exfalso
    have := blockLen_growth hM h
    omega

/-- Below the `j`-th block, all elements of the constructed set are very small. -/
