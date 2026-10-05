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

theorem szemerediFinitaryAt_of_forall_hasAP (k : ℕ)
    (h : ∀ A : Set ℕ, HasPosUpperDensity A → HasAP A k) : SzemerediFinitaryAt k := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · exact szemerediFinitaryAt_of_le_two (by omega)
  by_contra hcon
  unfold SzemerediFinitaryAt at hcon
  push_neg at hcon
  obtain ⟨δ, hδ, hbad⟩ := hcon
  -- extract, for every threshold `N`, a progression-free dense subset of some `[0, M)`
  have hbad' : ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ S : Finset ℕ, S ⊆ Finset.range M ∧
      δ * (M : ℝ) ≤ (S.card : ℝ) ∧ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
    intro N
    obtain ⟨M, hNM, S, hS, hcard, hno⟩ := hbad N
    exact ⟨M, hNM, S, hS, hcard, by
      rintro ⟨a, d, hd, hAP⟩
      obtain ⟨i, hi, hi'⟩ := hno a d hd
      exact hi' (hAP i hi)⟩
  choose Mf hM Sf hSub hCard hNo using hbad'
  have hpos := hasPosUpperDensity_blockUnion hδ hM hSub hCard
  exact not_hasAP_blockUnion (by omega) hM hSub hNo (h _ hpos)

/-- **Equivalence.** The finitary Szemerédi property is equivalent to the statement that
every subset of `ℕ` of positive upper density contains arbitrarily long arithmetic
progressions.  In particular the hypothesis of `Frontier.furstenberg_szemeredi` is not
stronger than its conclusion. -/
