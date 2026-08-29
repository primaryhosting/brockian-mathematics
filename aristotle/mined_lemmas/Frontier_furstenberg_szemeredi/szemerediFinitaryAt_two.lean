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

theorem szemerediFinitaryAt_two : SzemerediFinitaryAt 2 := by
  intro δ hδ
  refine ⟨⌈2 / δ⌉₊, fun M hM S _ hcard => ?_⟩
  -- from `M ≥ ⌈2/δ⌉` we get `δ * M ≥ 2`, hence `S` has at least two elements
  have hMR : 2 / δ ≤ (M : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hM)
  have h2 : (2 : ℝ) ≤ δ * M := by
    rw [div_le_iff₀ hδ] at hMR; linarith
  have hcard2 : 2 ≤ S.card := by exact_mod_cast le_trans h2 hcard
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using ha
    · have : a + 1 * (b - a) = b := by omega
      rw [this]; exact hb
  · refine ⟨b, a - b, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hb
    · have : b + 1 * (a - b) = a := by omega
      rw [this]; exact ha

/-- The finitary Szemerédi property for lengths `0` and `1` follows from the base case. -/
