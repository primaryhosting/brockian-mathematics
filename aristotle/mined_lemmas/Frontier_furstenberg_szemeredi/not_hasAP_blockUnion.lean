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

theorem not_hasAP_blockUnion {k : ℕ} (hk : 3 ≤ k) (hM : ∀ N, N ≤ Mf N)
    (hSub : ∀ N, Sf N ⊆ Finset.range (Mf N))
    (hNo : ∀ N, ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Sf N) :
    ¬ HasAP (blockUnion Mf Sf) k := by
  rintro ⟨a, d, hd, hAP⟩
  -- the largest term of the progression determines a block `j`
  have htop : a + (k - 1) * d ∈ blockUnion Mf Sf := hAP (k - 1) (by omega)
  obtain ⟨j, hj⟩ := (mem_blockUnion_iff _).mp htop
  obtain ⟨hb1, hb2⟩ := blockSet_bounds hSub hj
  have hLpos : 0 < blockLen Mf j := blockLen_pos hM j
  have hmono : ∀ i, i < k → a + i * d ≤ a + (k - 1) * d := by
    intro i hi
    have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  by_cases hcase : 2 * blockLen Mf j ≤ a
  · -- every term lies in the block `j`, contradicting progression-freeness of the block
    refine hNo (blockArg Mf j) ⟨a - 2 * blockLen Mf j, d, hd, fun i hi => ?_⟩
    have hmem : a + i * d ∈ blockUnion Mf Sf := hAP i hi
    have hle := hmono i hi
    have hin : a + i * d ∈ blockSet Mf Sf j :=
      blockSet_of_mem_blockUnion hM hSub hmem (by omega) (by omega)
    obtain ⟨s, hs, hseq⟩ := (mem_blockSet_iff _ _).mp hin
    have hrw : a - 2 * blockLen Mf j + i * d = s := by omega
    rw [hrw]; exact hs
  · -- otherwise the progression jumps over the (long) gap preceding the block `j`
    push_neg at hcase
    have hex : ∃ i, 2 * blockLen Mf j ≤ a + i * d := ⟨k - 1, hb1⟩
    have hmspec : 2 * blockLen Mf j ≤ a + Nat.find hex * d := Nat.find_spec hex
    have hm0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h] at hmspec
      simp at hmspec
      omega
    have hmin : ¬ (2 * blockLen Mf j ≤ a + (Nat.find hex - 1) * d) :=
      Nat.find_min hex (by omega)
    push_neg at hmin
    have hmk : Nat.find hex ≤ k - 1 := Nat.find_le hb1
    have hprev : a + (Nat.find hex - 1) * d ∈ blockUnion Mf Sf := hAP _ (by omega)
    have hsmall : 100 * (a + (Nat.find hex - 1) * d) < blockLen Mf j :=
      small_of_lt_block hM hSub hprev hmin
    have hstep : a + Nat.find hex * d = (a + (Nat.find hex - 1) * d) + d := by
      have hm1 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      calc a + Nat.find hex * d = a + (Nat.find hex - 1 + 1) * d := by rw [hm1]
        _ = (a + (Nat.find hex - 1) * d) + d := by ring
    have hspan : (k - 1) * d ≤ 3 * blockLen Mf j := le_of_lt (by omega)
    have h2d : 2 * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega

end Converse

/-- **Converse reduction.** If every set of positive upper density contains an arithmetic
progression of length `k`, then the finitary Szemerédi property holds at `k`. -/
