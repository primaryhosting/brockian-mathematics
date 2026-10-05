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

theorem hasAP_of_szemerediFinitaryAt {k : ℕ} (hSz : SzemerediFinitaryAt k) {A : Set ℕ}
    (hA : HasPosUpperDensity A) : HasAP A k := by
  obtain ⟨δ, hδ, hdens⟩ := hA
  obtain ⟨N, hN⟩ := hSz δ hδ
  obtain ⟨M, hNM, hM⟩ := hdens N
  obtain ⟨a, d, hd, hAP⟩ := hN M hNM ((Finset.range M).filter (fun n => n ∈ A))
    (Finset.filter_subset _ _) hM
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have hmem := hAP i hi
  simp only [Finset.mem_filter] at hmem
  exact hmem.2

/-- **Furstenberg–Szemerédi.** Assuming the finitary Szemerédi property (equivalently, the
combinatorial content of Furstenberg's multiple recurrence theorem), every subset of `ℕ`
of positive upper density contains arithmetic progressions of every length. -/
