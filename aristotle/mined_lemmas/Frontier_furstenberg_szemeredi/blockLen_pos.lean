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

theorem blockLen_pos (hM : ∀ N, N ≤ Mf N) (j : ℕ) : 0 < blockLen Mf j := by
  have := blockArg_le_blockLen hM j
  have h : 0 < blockArg Mf j := by
    cases j with
    | zero => simp [blockArg]
    | succ j => simp [blockArg]
  omega

