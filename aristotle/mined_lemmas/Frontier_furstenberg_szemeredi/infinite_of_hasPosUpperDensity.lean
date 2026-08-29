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

theorem infinite_of_hasPosUpperDensity {A : Set ℕ} (hA : HasPosUpperDensity A) : A.Infinite := by
  obtain ⟨δ, hδ, h⟩ := hA
  by_contra hc
  rw [Set.not_infinite] at hc
  obtain ⟨N, hN⟩ := exists_nat_gt ((hc.toFinset.card : ℝ) / δ)
  obtain ⟨M, hNM, hM⟩ := h N
  have hsub : ((Finset.range M).filter (fun n => n ∈ A)) ⊆ hc.toFinset := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    simpa using hx.2
  have hcard : ((((Finset.range M).filter (fun n => n ∈ A)).card : ℝ)) ≤ hc.toFinset.card := by
    exact_mod_cast Finset.card_le_card hsub
  have h1 : (hc.toFinset.card : ℝ) < δ * N := by
    rw [div_lt_iff₀ hδ] at hN; linarith
  have h2 : δ * (N : ℝ) ≤ δ * M := by
    have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
    nlinarith
  linarith

/-- **Unconditional base case of Furstenberg–Szemerédi.** A set of positive upper density
contains a two-term arithmetic progression. -/
