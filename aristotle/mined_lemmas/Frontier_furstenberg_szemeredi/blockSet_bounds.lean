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

theorem blockSet_bounds (hSub : ∀ N, Sf N ⊆ Finset.range (Mf N)) {j x : ℕ}
    (hx : x ∈ blockSet Mf Sf j) :
    2 * blockLen Mf j ≤ x ∧ x < 3 * blockLen Mf j := by
  rw [mem_blockSet_iff] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have : s < Mf (blockArg Mf j) := Finset.mem_range.mp (hSub _ hs)
  simp only [blockLen]
  omega

